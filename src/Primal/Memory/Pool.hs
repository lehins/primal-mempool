{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE NamedFieldPuns #-}
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
module Primal.Memory.Pool
  ( Pool
  , initPool
  , Block(..)
  , blockByteCount
  , grabNextFMAddr
  , grabNextMForeignPtr
  -- * Exported for testing
  , findNextZeroIndex
  , countPages
  ) where

import Control.Applicative
import Data.Bits
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
  -- have 64 blocks per group. For example, if program is compiled on a 64 bit OS and you
  -- know ahead of time the maximum number of blocks that will be allocated through out
  -- the program, then the optimal value for this argument will @maxBlockNum/64@
  -> (forall a. Count Word8 -> ST s (MForeignPtr a s))
  -- ^ Mempool page allocator. Some allocated pages might be immediately discarded,
  -- therefore number of pages utilized will not necessesarely match the number of times
  -- this action will be called.
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


-- | Useful function for testing. Check how many pages have been allocated thus far.
countPages :: Primal s m => Pool n s -> m Int
countPages pool = go 1 (poolFirstPage pool)
  where
    go n Page {pageNextPage} = do
      readBRef pageNextPage >>= \case
        Nothing -> pure n
        Just nextPage -> go (n + 1) nextPage


grabNextMForeignPtr :: (Primal s m, KnownNat n) => Pool n s -> m (MForeignPtr (Block n) s)
grabNextMForeignPtr = grabNextPoolBlockWith grabNextPageForeignPtr
{-# INLINE grabNextMForeignPtr #-}

grabNextFMAddr :: (Primal s m, KnownNat n) => Pool n s -> m (FMAddr (Block n) s)
grabNextFMAddr = grabNextPoolBlockWith grabNextPageFMAddr
{-# INLINE grabNextFMAddr #-}


grabNextPoolBlockWith ::
     Primal s m
  => (Page n s -> (Ptr (Block n) -> IO ()) -> m (Maybe (f (Block n) s)))
  -> Pool n s
  -> m (f (Block n) s)
grabNextPoolBlockWith grabNext pool = go (poolFirstPage pool)
  where
    go page = do
      isPageFull <- atomicReadURef (pageFull page)
      if isPageFull
        then atomicReadMutRef (pageNextPage page) >>= \case
               Nothing -> do
                 newPage <- liftST (poolPageInitializer pool)
                 -- There is a slight chance of a race condition in that the next page could
                 -- have been allocated and assigned to 'pageNextPage' by another thread
                 -- since we last checked for it. This is not a problem since we can safely
                 -- discard the page created in this thread and switch to the one that was
                 -- assigned to 'pageNextPage'.
                 mNextPage <-
                   atomicModifyMutRef (pageNextPage page) $ \mNextPage ->
                     (mNextPage <|> Just newPage, mNextPage)
                 case mNextPage of
                   Nothing -> go newPage
                   Just existingPage -> do
                     -- Here we cleanup the newly allocated page in favor of the one that
                     -- was potentially created by another thread. It is important to
                     -- eagerly free up scarce resources
                     unsafeIOToPrimal $
                       unsafeCastDataState (pageMemory newPage) >>= finalizeMForeignPtr
                     go existingPage
               Just nextPage -> go nextPage
        else grabNext page (poolBlockFinalizer pool) >>= \case
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
  grabNextPageWithAllocator page $ \blockPtr resetIndex -> unsafeIOToPrimal $ do
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
  -> (Ptr (Block n) -> IO () -> IO (f (Block n) RW))
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
    Just ix -> do
      fm <- withMForeignPtr pageMemory $ \pagePtr ->
        let !blockPtr =
              plusByteOffPtr pagePtr $
              Off ix * countToOff (blockByteCount (Block :: Block n))
         in unsafeIOToPrimal $ allocator blockPtr $ do
              let !(!q, !r) = ix `quotRem` ixBitSize
                  !pageBitMask = clearBit maxBound r
              touch pageMemory
              pageBitArrayIO <- unsafeCastDataState pageBitArray
              _ <- atomicAndFetchNewMutArray pageBitArrayIO q pageBitMask
              pageFullIO <- unsafeCastDataState pageFull
              atomicWriteURef pageFullIO False
      Just <$> unsafeCastDataState fm
{-# INLINE grabNextPageWithAllocator #-}



findNextZeroIndex :: forall b. FiniteBits b => b -> Maybe Int
findNextZeroIndex b =
  let !i0 = countTrailingZeros b
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
    f i !w =
      case findNextZeroIndex w of
        Nothing -> (w, Nothing)
        Just !bitIx -> (setBit w bitIx, Just (ixBitSize * i + bitIx))
{-# INLINE setNextZero #-}
