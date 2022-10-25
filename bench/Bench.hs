{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeApplications #-}

module Main where

import Foreign.Marshal.Alloc
import Primal.Monad
import GHC.TypeLits
import Criterion.Main
import Primal.Memory.Pool
import Primal.Memory.ForeignPtr
import Primal.Eval
import UnliftIO.Async

instance NFData (Pool n s) where
  rnf !_ = ()

instance NFData (ForeignPtr a) where
  rnf !_ = ()

instance NFData (MForeignPtr a s) where
  rnf !_ = ()

initHaskellPool :: KnownNat n => Int -> IO (Pool n RW)
initHaskellPool n = initPool n (fmap MForeignPtr . mallocByteCountForeignPtr) (const (pure ()))

cmallocForeignPtr :: Int -> IO (ForeignPtr a)
cmallocForeignPtr n = do
  ptr <- mallocBytes n
  newForeignPtr finalizerFree ptr

main :: IO ()
main = do
  let n = 10240
      blockSize = 32
  defaultMain
    [ bgroup "Optimal"
      [ env (initHaskellPool @32 (n `div` 64)) $ \pool ->
          bench "FMAddr" $ nfIO (replicateM n (grabNextPoolFMAddr pool))
      , env (initHaskellPool @32 (n `div` 64)) $ \pool ->
          bench "MForeignPtr" $ nfIO (replicateM n (grabNextPoolMForeignPtr pool))
      , bench "ForeignPtr (ByteArray)" $
          nfIO (replicateM n (mallocByteCountForeignPtr (fromIntegral blockSize)))
      , bench "ForeignPtr (malloc)" $
          nfIO (replicateM n (cmallocForeignPtr blockSize))
      ]
    , bgroup "Concurrent"
      [ env (initHaskellPool @32 (n `div` 64)) $ \pool ->
          bench "FMAddr" $ nfIO (pooledReplicateConcurrently n (grabNextPoolFMAddr pool))
      , env (initHaskellPool @32 (n `div` 64)) $ \pool ->
          bench "MForeignPtr" $ nfIO (pooledReplicateConcurrently n (grabNextPoolMForeignPtr pool))
      , bench "ForeignPtr (ByteArray)" $
          nfIO (pooledReplicateConcurrently n (mallocByteCountForeignPtr (fromIntegral blockSize)))
      , bench "ForeignPtr (malloc)" $
          nfIO (pooledReplicateConcurrently n (cmallocForeignPtr blockSize))
      ]
    ]
