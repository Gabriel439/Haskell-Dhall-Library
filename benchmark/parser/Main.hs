{-# LANGUAGE OverloadedStrings #-}

module Main where

import Control.Monad (forM)
import Criterion.Main (defaultMain, bgroup, bench, whnf, nfIO)
import Data.Map (Map, foldrWithKey, singleton, unions)

import System.Directory

import qualified Codec.Serialise
import qualified Criterion.Main as Criterion
import qualified Data.ByteString.Lazy
import qualified Data.Text as T
import qualified Data.Text.IO as TIO
import qualified Dhall.Binary
import qualified Dhall.Parser as Dhall

type PreludeFiles = Map FilePath T.Text

loadPreludeFiles :: IO PreludeFiles
loadPreludeFiles = loadDirectory "Prelude"
    where
        loadDirectory :: FilePath -> IO PreludeFiles
        loadDirectory dir =
            withCurrentDirectory dir $ do
                files <- getCurrentDirectory >>= listDirectory
                results <- forM files $ \file -> do
                    file' <- makeAbsolute file
                    doesExist <- doesFileExist file'
                    if doesExist
                       then loadFile file'
                       else loadDirectory file'
                pure $ unions results

        loadFile :: FilePath -> IO PreludeFiles
        loadFile path = singleton path <$> TIO.readFile path

benchParser :: PreludeFiles -> Criterion.Benchmark
benchParser =
      bgroup "exprFromText"
    . foldrWithKey (\name expr -> (benchExprFromText name expr :)) []

benchExprFromText :: String -> T.Text -> Criterion.Benchmark
benchExprFromText name expr =
    bench name $ whnf (Dhall.exprFromText "(input)") expr

benchExprFromBytes
    :: String -> Data.ByteString.Lazy.ByteString -> Criterion.Benchmark
benchExprFromBytes name bytes = bench name (whnf f bytes)
  where
    f bytes = do
        term <- case Codec.Serialise.deserialiseOrFail bytes of
            Left  _    -> Nothing
            Right term -> return term
        case Dhall.Binary.decode term of
            Left  _          -> Nothing
            Right expression -> return expression

main :: IO ()
main = do
    prelude <- loadPreludeFiles
    issue108Text  <- TIO.readFile "benchmark/examples/issue108.dhall"
    issue108Bytes <- Data.ByteString.Lazy.readFile "benchmark/examples/issue108.dhall.bin"
    defaultMain
        [ bgroup "Issue #108"
            [ benchExprFromText  "Text"   issue108Text
            , benchExprFromBytes "Binary" issue108Bytes
            ]
        , benchExprFromText "Long variable names" (T.replicate 1000000 "x")
        , benchExprFromText "Large number of function arguments" (T.replicate 10000 "x ")
        , benchExprFromText "Long double-quoted strings" ("\"" <> T.replicate 1000000 "x" <> "\"")
        , benchExprFromText "Long single-quoted strings" ("''" <> T.replicate 1000000 "x" <> "''")
        , benchExprFromText "Whitespace" (T.replicate 1000000 " " <> "x")
        , benchExprFromText "Line comment" ("x -- " <> T.replicate 1000000 " ")
        , benchExprFromText "Block comment" ("x {- " <> T.replicate 1000000 " " <> "-}")
        , benchExprFromText "Deeply nested parentheses" "((((((((((((((((x))))))))))))))))"
        , benchParser prelude
        ]
