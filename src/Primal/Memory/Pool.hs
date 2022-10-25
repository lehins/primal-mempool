{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- |
-- Module      : Primal.Memory.Pool
-- Copyright   : (c) Alexey Kuleshevich 2022
-- License     : BSD3
-- Maintainer  : Alexey Kuleshevich <alexey@kuleshevi.ch>
-- Stability   : experimental
-- Portability : non-portable
module Primal.Memory.Pool where

import Control.Applicative
import Data.Bits
import Data.Maybe
import GHC.TypeLits
import Primal.Array.Boxed
import Primal.Array.Unboxed
import Primal.Container.Array
import Primal.Container.Ref
import Primal.Eval
import Primal.Memory
import Primal.Memory.FAddr
import Primal.Memory.ForeignPtr
import Primal.Memory.Ptr
import Primal.Monad.Unsafe
import Primal.Ref

data Block (n :: Nat) = Block

blockByteCount :: KnownNat n => Block n -> Count Word8
blockByteCount = fromInteger . natVal

data Page n s =
  Page
    { pageMemory :: !(MForeignPtr (Block n) s)
    , pageBitArray :: !(UMArray Word s)
    , pageFull :: !(URef Bool s)
    , pageNextPage :: !(BRef (Maybe (Page n s)) s)
    }

data Pool n s =
  Pool
    { poolFirstPage :: !(Page n s)
    , poolPageInitializer :: ST s (Page n s)
    , poolBlockFinalizer :: Ptr (Block n) -> IO ()
    }

ixBitSize :: Int
ixBitSize = finiteBitSize (0 :: Word)

initPool ::
     forall n m s. (KnownNat n, Primal s m)
  => Int
  -- ^ Number of groups per page. Must be a posititve number, otherwise error. One group
  -- contains as many blocks as the operating system has bits. A 64bit architecture will
  -- have 64 blocks per group.
  -> (forall a. Count Word8 -> ST s (MForeignPtr a s))
  -- ^ Mempool page allocator. Some allocated pages might be immediately discarded.
  -> (Ptr (Block n) -> IO ())
  -- ^ Finalizer to use for each block. It is an IO action because it will be executed by
  -- the Garbage Collector in a separate thread once the `Block` is no longer referenced.
  -> m (Pool n s)
initPool groupsPerPage memAlloc blockFinalizer = do
  unless (groupsPerPage > 0) $
    error $
    "Groups per page should be a positive number, but got: " ++
    show groupsPerPage
  let pageInit = do
        pageMemory <-
          memAlloc $
          Count (groupsPerPage * ixBitSize) * blockByteCount (Block :: Block n)
        pageBitArray <- newUMArray (Size groupsPerPage) 0
        pageFull <- newURef False
        pageNextPage <- newBRef Nothing
        pure Page {..}
  firstPage <- liftST pageInit
  pure
    Pool
      { poolFirstPage = firstPage
      , poolPageInitializer = pageInit
      , poolBlockFinalizer = blockFinalizer
      }

grabNextPoolMForeignPtr :: (Primal s m, KnownNat n) => Pool n s -> m (MForeignPtr (Block n) s)
grabNextPoolMForeignPtr = grabNextPoolBlockWith grabNextPageForeignPtr
{-# INLINE grabNextPoolMForeignPtr #-}

grabNextPoolFMAddr :: (Primal s m, KnownNat n) => Pool n s -> m (FMAddr (Block n) s)
grabNextPoolFMAddr = grabNextPoolBlockWith grabNextPageFMAddr
{-# INLINE grabNextPoolFMAddr #-}


grabNextPoolBlockWith ::
     Primal s m
  => (Page n s -> (Ptr (Block n) -> IO ()) -> m (Maybe (f (Block n) s)))
  -> Pool n s
  -> m (f (Block n) s)
grabNextPoolBlockWith grabNext pool = go (poolFirstPage pool)
  where
    go !page@Page {..} = do
      isPageFull <- atomicReadURef pageFull
      if isPageFull
        then do
          atomicReadMutRef pageNextPage >>= \case
            Nothing -> do
              newPage <- liftST (poolPageInitializer pool)
              -- There is a slight chance of a race condition in that the next page could
              -- have been allocated and assigned to 'pageNextPage' by another thread
              -- since we last checked for it. This is not a problem since we can safely
              -- discard the page created in this thread and switch to the one that was
              -- assigned to 'pageNextPage'.
              mNextPage <-
                atomicModifyMutRef pageNextPage $ \mNextPage ->
                  (mNextPage <|> Just newPage, mNextPage)
              -- Here we potentially discard the newly allocated page in favor of the one
              -- created by another thread.
              go (fromMaybe newPage mNextPage)
            Just nextPage -> go nextPage
        else
          grabNext page (poolBlockFinalizer pool) >>= \case
            Nothing -> go page
            Just ma -> pure ma
{-# INLINE grabNextPoolBlockWith #-}


grabNextPageFMAddr ::
     forall n m s.
     (Primal s m, KnownNat n)
  -- | Page to grab the block from
  => Page n s
  -- | Finalizer to run, once the `FMAddr` to the block is no longer used
  -> (Ptr (Block n) -> IO ())
  -> m (Maybe (FMAddr (Block n) s))
grabNextPageFMAddr page finalizer =
  grabNextPageWithAllocator page $ \blockPtr resetIndex ->
    allocWithFinalizerFMAddr 1 (const (pure blockPtr)) $ \ptr ->
      finalizer ptr >> resetIndex
{-# INLINE grabNextPageFMAddr #-}


grabNextPageForeignPtr ::
     forall n m s.
     (Primal s m, KnownNat n)
  -- | Page to grab the block from
  => Page n s
  -- | Finalizer to run, once the `FMAddr` to the block is no longer used
  -> (Ptr (Block n) -> IO ())
  -> m (Maybe (MForeignPtr (Block n) s))
grabNextPageForeignPtr page finalizer =
  grabNextPageWithAllocator page $ \blockPtr resetIndex -> do
    fp <- newForeignPtr_ blockPtr
    addForeignPtrConcFinalizer fp $ finalizer blockPtr >> resetIndex
    pure $ MForeignPtr fp
{-# INLINE grabNextPageForeignPtr #-}

grabNextPageWithAllocator ::
     forall f n m s. (Primal s m, KnownNat n)
  => Page n s
  -> (Ptr (Block n) -> IO () -> IO (f (Block n) s))
  -> m (Maybe (f (Block n) s))
grabNextPageWithAllocator Page {..} allocator = do
  setNextZero pageBitArray >>= \case
    -- There is a slight chance that some Blocks will be cleared before the pageFull is
    -- set to True. This is not a problem because that memory will be recovered as soon as
    -- any other Block in the Page is finalized
    --
    -- TODO: Potentially verify that first Word in pageBitArray is still maxBound, in
    -- order to prevent the degenerate case of all Blocks beeing finalized right before
    -- the page is marked as full.
    Nothing -> Nothing <$ atomicWriteURef pageFull True
    Just ix ->
      fmap Just $
      withMForeignPtr pageMemory $ \pagePtr ->
        let blockPtr =
              plusByteOffPtr pagePtr $
              Off ix * countToOff (blockByteCount (Block :: Block n))
         in unsafeIOToPrimal $ allocator blockPtr $ do
              let (q, r) = ix `quotRem` ixBitSize
              touch pageMemory
              pageBitArrayIO <- unsafeCastDataState pageBitArray
              _ <- atomicAndFetchNewMutArray pageBitArrayIO q (clearBit maxBound r)
              pageFullIO <- unsafeCastDataState pageFull
              atomicWriteURef pageFullIO False
{-# INLINE grabNextPageWithAllocator #-}



findNextZeroIndex :: forall b. FiniteBits b => b -> Maybe Int
findNextZeroIndex b =
  let i0 = countTrailingZeros b
      i1 = countTrailingZeros (complement b)
      maxBits = finiteBitSize (undefined :: b)
   in if i0 == 0
        then if i1 == maxBits
               then Nothing
               else Just i1
        else Just (i0 - 1)
{-# INLINE findNextZeroIndex #-}

setNextZero :: Primal s m => UMArray Word s -> m (Maybe Int)
setNextZero ma = ifindAtomicMutArray ma f
  where
    f i w =
      case findNextZeroIndex w of
        Nothing -> (w, Nothing)
        Just bitIx -> (setBit w bitIx, Just (ixBitSize * i + bitIx))
{-# INLINE setNextZero #-}
