{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
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

import Data.Bits
import GHC.TypeLits
import Primal.Array.Boxed
import Primal.Array.Unboxed
import Primal.Concurrent.MVar
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
    , pagePrevPage :: !(BRef (Maybe (Page n s)) s)
    }

data Pool n s =
  Pool
    { poolLastPage :: !(MVar (Page n s) s)
    , poolPageInitializer :: ST s (Page n s)
    , poolBlockFinalizer :: Ptr (Block n) -> IO ()
    }

ixBitSize :: Int
ixBitSize = finiteBitSize (0 :: Word)

initPool ::
     forall n m. (KnownNat n, Primal RW m)
  => Int
  -- ^ Number of groups per page. Must be a posititve number, otherwise error. One group
  -- contains as many blocks as the operating system has bits. A 64bit architecture will
  -- have 64 blocks per group. For example, if program is compiled on a 64 bit OS and you
  -- know ahead of time the maximum number of blocks that will be allocated through out
  -- the program, then the optimal value for this argument will @maxBlockNum/64@
  -> (forall a. Count Word8 -> ST RW (MForeignPtr a RW))
  -- ^ Mempool page allocator. Some allocated pages might be immediately discarded,
  -- therefore number of pages utilized will not necessesarely match the number of times
  -- this action will be called.
  -> (Ptr (Block n) -> IO ())
  -- ^ Finalizer to use for each block. It is an IO action because it will be executed by
  -- the Garbage Collector in a separate thread once the `Block` is no longer referenced.
  -> m (Pool n RW)
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
        pagePrevPage <- newBRef Nothing
        pure Page {..}
  firstPage <- newMVar =<< liftST pageInit
  pure
    Pool
      { poolLastPage = firstPage
      , poolPageInitializer = pageInit
      , poolBlockFinalizer = blockFinalizer
      }


-- | Useful function for testing. Check how many pages have been allocated thus far.
countPages :: Primal s m => Pool n s -> m Int
countPages pool = readMVar (poolLastPage pool) >>= go 1
  where
    go n Page {pagePrevPage} = do
      readBRef pagePrevPage >>= \case
        Nothing -> pure n
        Just nextPage -> go (n + 1) nextPage


grabNextMForeignPtr :: (Primal RW m, KnownNat n) => Pool n RW -> m (MForeignPtr (Block n) RW)
grabNextMForeignPtr = grabNextPoolBlockWith grabNextPageForeignPtr
{-# INLINE grabNextMForeignPtr #-}

grabNextFMAddr :: (Primal RW m, KnownNat n) => Pool n RW -> m (FMAddr (Block n) RW)
grabNextFMAddr = grabNextPoolBlockWith grabNextPageFMAddr
{-# INLINE grabNextFMAddr #-}


grabNextPoolBlockWith ::
     Primal RW m
  => (Page n RW -> (Ptr (Block n) -> IO ()) -> m (Maybe (f (Block n) RW)))
  -> Pool n RW
  -> m (f (Block n) RW)
grabNextPoolBlockWith grabNext pool = readMVar (poolLastPage pool) >>= go
  where
    go page = do
      isPageFull <- atomicReadURef (pageFull page)
      if isPageFull
        then atomicReadMutRef (pagePrevPage page) >>= \case
               Nothing ->
                 join $ liftIO $ modifyMVar (poolLastPage pool) $ \ lastPage -> do
                   newPage <- liftST $ poolPageInitializer pool
                   atomicWriteBRef (pagePrevPage newPage) $ Just lastPage
                   pure (newPage, go newPage)
               Just nextPage -> go nextPage
        else grabNext page (poolBlockFinalizer pool) >>= \case
               Nothing -> go page
               Just ma -> pure ma
{-# INLINE grabNextPoolBlockWith #-}


grabNextPageFMAddr ::
     forall n m.
     (Primal RW m, KnownNat n)
  -- | Page to grab the block from
  => Page n RW
  -- | Finalizer to run, once the `FMAddr` to the block is no longer used
  -> (Ptr (Block n) -> IO ())
  -> m (Maybe (FMAddr (Block n) RW))
grabNextPageFMAddr page finalizer =
  grabNextPageWithAllocator page $ \blockPtr resetIndex -> unsafeIOToPrimal $ do
    allocWithFinalizerFMAddr 1 (const (pure blockPtr)) $ \ptr ->
      finalizer ptr >> resetIndex
{-# INLINE grabNextPageFMAddr #-}


grabNextPageForeignPtr ::
     forall n m.
     (Primal RW m, KnownNat n)
  -- | Page to grab the block from
  => Page n RW
  -- | Finalizer to run, once the `FMAddr` to the block is no longer used
  -> (Ptr (Block n) -> IO ())
  -> m (Maybe (MForeignPtr (Block n) RW))
grabNextPageForeignPtr page finalizer =
  grabNextPageWithAllocator page $ \blockPtr resetIndex -> do
    fp <- newForeignPtr_ blockPtr
    addForeignPtrConcFinalizer fp $ finalizer blockPtr >> resetIndex
    pure $ MForeignPtr fp
{-# INLINE grabNextPageForeignPtr #-}

grabNextPageWithAllocator ::
     forall f n m. (Primal RW m, KnownNat n)
  => Page n RW
  -> (Ptr (Block n) -> IO () -> IO (f (Block n) RW))
  -> m (Maybe (f (Block n) RW))
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
