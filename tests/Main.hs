module Main where

import Spec
import System.IO (BufferMode (LineBuffering), hSetBuffering, hSetEncoding, stdout, utf8)
import Test.Hspec
import Test.Hspec.Runner

main :: IO ()
main = do
  hSetBuffering stdout LineBuffering
  hSetEncoding stdout utf8
  let config =
        defaultConfig {
        configTimes = True
        }
  hspecWith config spec
