{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import Data.Text            (Text)
import Test.Tasty           (TestTree)
import Test.Tasty.Silver    (findByExtension)
import System.FilePath      (takeBaseName, replaceExtension)

import qualified Data.Csv
import qualified Data.Text.IO
import qualified Dhall.Core         as D
import qualified Dhall.Csv
import qualified Dhall.CsvToDhall
import qualified Dhall.Csv.Util
import qualified GHC.IO.Encoding
import qualified Test.Tasty
import qualified Test.Tasty.Silver  as Silver


main :: IO ()
main = do
    GHC.IO.Encoding.setLocaleEncoding GHC.IO.Encoding.utf8

    testTree <- goldenTests
    Test.Tasty.defaultMain testTree

goldenTests :: IO TestTree
goldenTests = do
    dhallToCsvTree <- dhallToCsvGolden
    csvToDhallTree <- csvToDhallGolden
    return $ Test.Tasty.testGroup "dhall-csv"
        [ dhallToCsvTree
        , csvToDhallTree
        ]

dhallToCsvGolden :: IO TestTree
dhallToCsvGolden = do
    dhallFiles <- findByExtension [".dhall"] "./tasty/data/dhall-to-csv"
    return $ Test.Tasty.testGroup "dhall-to-csv"
        [ Silver.goldenVsAction
            (takeBaseName dhallFile)
            csvFile
            (Dhall.Csv.codeToValue Nothing =<< Data.Text.IO.readFile dhallFile)
            Dhall.Csv.Util.encodeCsvDefault
        | dhallFile <- dhallFiles
        , let csvFile = replaceExtension dhallFile ".csv"
        ]

csvToDhallGolden :: IO TestTree
csvToDhallGolden = do
    csvFiles <- findByExtension [".csv"] "./tasty/data/csv-to-dhall"
    return $ Test.Tasty.testGroup "csv-to-dhall"
        [ Silver.goldenVsAction
            (takeBaseName csvFile)
            dhallFile
            (textToCsv =<< Data.Text.IO.readFile csvFile)
            (D.pretty . Dhall.CsvToDhall.dhallFromCsv)
        | csvFile <- csvFiles
        , let dhallFile = replaceExtension csvFile ".dhall"
        ]

textToCsv :: Text -> IO [Data.Csv.NamedRecord]
textToCsv txt =
    case Dhall.Csv.Util.decodeCsvDefault txt of
        Left err -> fail err
        Right csv -> return csv
