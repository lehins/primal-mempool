{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}

module Test.Primal.Memory.PoolSpec (spec) where

import Common
import Control.Concurrent (threadDelay)
import Control.Concurrent.Async
import Control.Concurrent.Chan
import Data.Bits
import Data.Function
import Data.Reflection
import GHC.TypeNats
import Primal.Eval
import Primal.Memory
import Primal.Memory.FAddr
import Primal.Memory.ForeignPtr
import Primal.Memory.GC (performGC)
import Primal.Memory.Pool
import Primal.Memory.Ptr
import Primal.Ref.Unboxed
import Primal.Ref.Unboxed.Atomic
import System.Random.Stateful


spec :: Spec
spec = do
  describe "Pool" $ do
    prop "findNextZeroIndex" $ propFindNextZeroIndex
    describe "MForeignPtr" $ do
      poolProps grabNextMForeignPtr finalizeMForeignPtr (Block :: Block 32)
      poolProps grabNextMForeignPtr finalizeMForeignPtr (Block :: Block 64)
      poolPropsArbSizeBlockMForeignPtr
    describe "FMAddr" $ do
      poolProps grabNextFMAddr finalizeFMAddr (Block :: Block 32)
      poolProps grabNextFMAddr finalizeFMAddr (Block :: Block 64)
      poolPropsArbSizeBlockFMAddr

poolProps ::
     (KnownNat n, MemPtr (ma (Block n)))
  => (Pool n RW -> IO (ma (Block n) RW))
  -> (ma (Block n) RW -> IO ())
  -> Block n
  -> Spec
poolProps grabNext finalize block =
  describe ("Block " ++ show (blockByteCount block)) $ do
    prop "PoolGarbageCollected" $ propPoolGarbageCollected grabNext block
    prop "PoolAllocateAndFinalize" $ propPoolAllocateAndFinalize grabNext finalize block

poolPropsArbSizeBlockMForeignPtr :: Spec
poolPropsArbSizeBlockMForeignPtr =
  describe "Arbitrary sized block" $ do
    prop "PoolGarbageCollected" $ \(Positive n) ->
      reifyNat n (propPoolGarbageCollected grabNextMForeignPtr . proxyToBlock)
    prop "PoolAllocateAndFinalize" $ \(Positive n) ->
      reifyNat n (propPoolAllocateAndFinalize grabNextMForeignPtr finalizeMForeignPtr . proxyToBlock)
  where
    proxyToBlock :: Proxy n -> Block n
    proxyToBlock Proxy = Block


poolPropsArbSizeBlockFMAddr :: Spec
poolPropsArbSizeBlockFMAddr =
  describe "Arbitrary sized block" $ do
    prop "PoolGarbageCollected" $ \(Positive n) ->
      reifyNat n (propPoolGarbageCollected grabNextFMAddr . proxyToBlock)
    prop "PoolAllocateAndFinalize" $ \(Positive n) ->
      reifyNat n (propPoolAllocateAndFinalize grabNextFMAddr finalizeFMAddr . proxyToBlock)
  where
    proxyToBlock :: Proxy n -> Block n
    proxyToBlock Proxy = Block


propFindNextZeroIndex :: Word -> Expectation
propFindNextZeroIndex w =
  case findNextZeroIndex w of
    Nothing -> w `shouldBe` maxBound
    Just ix -> do
      testBit w ix `shouldBe` False
      case findNextZeroIndex (setBit w ix) of
        Nothing -> setBit w ix `shouldBe` maxBound
        Just ix' -> do
          ix' `shouldNotBe` ix
          testBit w ix' `shouldBe` False

-- We allow one extra page be allocated due to concurrency false positives in block
-- reservations
checkNumPages :: Pool n RW -> Int -> Int -> Expectation
checkNumPages pool n numBlocks = do
  let estimatedUpperBoundOfPages = 1 + max 1 (numBlocks `div` n `div` 64)
  numPages <- countPages pool
  unless (numPages <= estimatedUpperBoundOfPages) $
    expectationFailure $
    concat
      [ "Number of pages should not exceed the expected amount: "
      , show estimatedUpperBoundOfPages
      , " but allocated: "
      , show numPages
      ]

checkBlockBytes ::
     (KnownNat n)
  => Block n
  -> Word8
  -> Ptr b
  -> Expectation
checkBlockBytes block byte ptr =
  let ptr8 = castPtr ptr
      checkFillByte i =
        when (i >= 0) $ do
          readOffPtr ptr8 i `shouldReturn` byte
          checkFillByte (i - 1)
   in checkFillByte (countToOff (blockByteCount block) - 1)


-- | Wait for all items to be GCed by periodicaly trigger garbage collector for certain
-- number of times before failing, unless the counter action was executed the exact number
-- of times.
ensureAllGCed ::
     Int
  -- ^ Number of time we expect the action supplied to below function must be executed
  -> (IO () -> IO a)
  -- ^ Run this action and wait until the argument is called in another thread the
  -- expected number of times
  -> IO a
ensureAllGCed n f = do
  countRef <- newURef (0 :: Int)
  res <- f (atomicAddURef_ countRef 1)
  let iters = 100
      go i = do
        let delay = 10 -- ms
        performGC
        -- allow some time for all blocks to finalize
        threadDelay (delay * 1000)
        n' <- atomicReadURef countRef
        unless (n' == n) $ do
          if i <= 1
            then expectationFailure $
                 "Expected all " ++
                 show n ++
                 " pointers to be GCed in " ++
                 show (delay * iters) ++
                 "ms, but " ++ show n' ++ " where GCed instead"
            else go (i - 1)
  res <$ go iters


mallocPreFilled :: forall a s. Word8 -> Count Word8 -> ST s (MForeignPtr a s)
mallocPreFilled preFillByte bc = do
  mut <- allocMutMem bc
  mut <$ setByteOffMutMem mut 0 bc preFillByte


propPoolGarbageCollected ::
     forall (ma :: * -> * -> *) n. (KnownNat n, MemPtr (ma (Block n)))
  => (Pool n RW -> IO (ma (Block n) RW))
  -> Block n
  -> Positive Int
  -> Word16
  -> Word8
  -> Word8
  -> Expectation
propPoolGarbageCollected grabNext block (Positive n) numBlocks16 preFillByte fillByte = do
  let numBlocks = 1 + (fromIntegral numBlocks16 `div` 20) -- make it not too big
  (pool, ptrs) <-
    ensureAllGCed numBlocks $ \countOneBlockGCed -> do
      pool <-
        initPool n (mallocPreFilled preFillByte) $ \ptr -> do
          setPtr (castPtr ptr) (blockByteCount block) fillByte
          countOneBlockGCed
      fmps :: [ma (Block n) RW] <-
        replicateConcurrently numBlocks (grabNext pool)
      touch fmps
      -- Here we return just the pointers and let the GC collect the ForeignPtrs
      ptrs <-
        forM fmps $ \fma ->
          withPtrMutMem fma $ \ptr -> do
            checkBlockBytes block preFillByte ptr
            ptr <$ setPtr ptr (blockByteCount block) fillByte
      pure (pool, ptrs)
  forM_ ptrs (checkBlockBytes block fillByte)
  checkNumPages pool n numBlocks
  -- Ensure that memory to that the pointers are referencing to is still alive
  touch pool


propPoolAllocateAndFinalize ::
     forall (ma :: * -> * -> *) n. (KnownNat n, MemPtr (ma (Block n)))
  => (Pool n RW -> IO (ma (Block n) RW))
  -> (ma (Block n) RW -> IO ())
  -> Block n
  -> Positive Int
  -> Word16
  -> Word8
  -> Word8
  -> Int
  -> Expectation
propPoolAllocateAndFinalize grabNext finalize block np numBlocks16 emptyByte fullByte seed = do
  let Positive n = np
      numBlocks = 1 + (fromIntegral numBlocks16 `div` 20)
  pool <-
    ensureAllGCed numBlocks $ \countOneBlockGCed -> do
      chan <- newChan
      pool <-
        initPool n (mallocPreFilled emptyByte) $ \(ptr :: Ptr (Block n)) -> do
          setPtr (castPtr ptr) (blockByteCount block) emptyByte
          countOneBlockGCed
      -- allocate and finalize blocks concurrently
      pool <$
        concurrently_
          (do replicateConcurrently_ numBlocks $ do
                fp <- grabNext pool
                withPtrMutMem fp (checkBlockBytes block emptyByte)
                writeChan chan (Just fp)
              -- place Nothing to indicate we are done allocating blocks
              writeChan chan Nothing)
          (runStateGenT_ (mkStdGen seed) $ \gen ->
             fix $ \loop -> do
               mfp <- liftIO $ readChan chan
               forM_ mfp $ \fp -> do
                 liftIO $ withPtrMutMem fp $ \ptr ->
                   -- fill the newly allocated block
                   setPtr ptr (blockByteCount block) fullByte
                 -- manually finalize every other block and let the GC to pick the rest
                 shouldFinalize <- uniformM gen
                 when shouldFinalize $ liftIO $ finalize fp
                 loop)
  -- verify number of pages
  checkNumPages pool n numBlocks
