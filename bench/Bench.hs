{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeApplications #-}

module Main where

import Primal.Monad
import GHC.TypeLits
import Criterion.Main
import Primal.Memory.Pool
import Primal.Memory.ForeignPtr
import Primal.Eval

instance NFData (Pool n s) where
  rnf !_ = ()

initHaskellPool :: KnownNat n => Int -> IO (Pool n RW)
initHaskellPool n = initPool n (fmap MForeignPtr . mallocByteCountForeignPtr) (const (pure ()))

main :: IO ()
main = do
  let n = 10000
  defaultMain
    [ bgroup "Pool"
      [ env (initHaskellPool @32 1) $ \pool ->
          bench "FMAddr 100000" $ whnfIO (replicateM n (grabNextPoolFMAddr pool))
      , bench "FMAddr 100000" $ whnfIO (replicateM n (mallocByteCountForeignPtr 32))
      ]
    ]
