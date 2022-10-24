{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}

module LibSpec (spec) where

import Common
import Control.Concurrent (threadDelay)
import Control.Concurrent.Async
import GHC.TypeNats
import Primal.Memory.FAddr
import Primal.Memory.ForeignPtr
import Primal.Memory
import Primal.Memory.GC (performGC)
import Primal.Memory.Pool
import Primal.Memory.Ptr
import Primal.Ref.Unboxed
import Primal.Ref.Unboxed.Atomic
import Primal.Eval
import Data.Bits


spec :: Spec
spec = do
  describe "Pool" $ do
    prop "findNextZeroIndex" $ propFindNextZeroIndex
    prop "First prop" $ propPool (Block :: Block 32)

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

propPool ::
     forall n. KnownNat n
  => Block n
  -> Positive Int
  -> Word16
  -> Word8
  -> Word8
  -> Expectation
propPool block (Positive n) numBlocks16 preFillByte fillByte = do
  let -- A fairly large positive number
      numBlocks = 1 + (fromIntegral numBlocks16 `div` 20)
      mallocZero bc = do
        mfp <- MForeignPtr <$> mallocByteCountForeignPtr bc
        withMForeignPtr mfp $ \ptr -> setOffPtr (castPtr ptr) 0 bc preFillByte
        pure mfp
      checkBlockBytes byte ptr =
        let checkFillByte i =
               when (i >= 0) $ do
                 readByteOffPtr ptr i `shouldReturn` byte
                 checkFillByte (i - 1)
        in checkFillByte (countToOff (blockByteCount block) - 1)
  countRef <- newURef (0 :: Int)
  pool <-
    initPool n mallocZero $ \ptr -> do
      setOffPtr (castPtr ptr) 0 (blockByteCount block) fillByte
      atomicAddURef_ countRef 1
  fmas :: [FMAddr (Block n) RW] <-
    replicateConcurrently numBlocks (grabNextPoolFMAddr pool)
  ptrsMAddrs <- forM fmas $ \fma ->
    withPtrFMAddr fma $ \ptr -> do
      let bytePtr = castPtr ptr
      checkBlockBytes preFillByte bytePtr
      setOffPtr bytePtr 0 (blockByteCount block) fillByte
      pure bytePtr
  fmps :: [MForeignPtr (Block n) RW] <-
    replicateConcurrently numBlocks (grabNextPoolMForeignPtr pool)
  touch fmas
  ptrsFPtrs <- forM fmps $ \fma ->
    withMForeignPtr fma $ \ptr -> do
      let bytePtr = castPtr ptr
      checkBlockBytes preFillByte bytePtr
      setOffPtr bytePtr 0 (blockByteCount block) fillByte
      pure bytePtr
  performGC
  threadDelay 50000
  atomicReadURef countRef `shouldReturn` (numBlocks * 2)
  forM_ ptrsMAddrs (checkBlockBytes fillByte)
  forM_ ptrsFPtrs (checkBlockBytes fillByte)
  touch pool
