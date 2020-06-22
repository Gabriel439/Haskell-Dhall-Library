{-# LANGUAGE OverloadedStrings #-}

module Main where

import Gauge (defaultMain, bgroup, bench, nf, env)

import Control.Exception (throw)
import qualified Gauge
import qualified Data.Text as T
import qualified Data.Text.IO as TIO
import qualified Dhall.Core as Dhall
import qualified Dhall.Parser as Dhall

benchExprFromText :: String -> T.Text -> Gauge.Benchmark
benchExprFromText name expr =
    bench name $ nf (either throw id . Dhall.exprFromText "(input)") expr

main :: IO ()
main = do
    defaultMain
        [ env cpkgExample $ \e ->
            benchExprFromText "CPkg/Text" e
        ]
    where cpkgExample = TIO.readFile "benchmark/normalize/cpkg.dhall"
