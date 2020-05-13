{-# LANGUAGE OverloadedLists   #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards   #-}

module Main where

import Data.Monoid ((<>))
import Dhall.JSON.Yaml (Options (..))
import Test.Tasty (TestTree)

import qualified Data.ByteString
import qualified Data.Text.IO
import qualified Dhall.Core
import qualified Dhall.JSON.Yaml
import qualified Dhall.Yaml
import qualified Dhall.YamlToDhall as YamlToDhall
import qualified GHC.IO.Encoding
import qualified Test.Tasty
import qualified Test.Tasty.HUnit

main :: IO ()
main = do
    GHC.IO.Encoding.setLocaleEncoding GHC.IO.Encoding.utf8

    Test.Tasty.defaultMain testTree

testTree :: TestTree
testTree =
    Test.Tasty.testGroup "dhall-yaml"
        [ testDhallToYaml
            Dhall.JSON.Yaml.defaultOptions
            "./tasty/data/normal"
            True
            False
        , testDhallToYaml
            Dhall.JSON.Yaml.defaultOptions
            "./tasty/data/normal-aeson"
            False
            True
        , testDhallToYaml
            Dhall.JSON.Yaml.defaultOptions
            "./tasty/data/special"
            True
            True
        , testDhallToYaml
            Dhall.JSON.Yaml.defaultOptions
            "./tasty/data/emptyList"
            True
            True
        , testDhallToYaml
            Dhall.JSON.Yaml.defaultOptions
            "./tasty/data/emptyMap"
            True
            True
        , testDhallToYaml
            (Dhall.JSON.Yaml.defaultOptions { quoted = True })
            "./tasty/data/quoted"
            False
            True
        , testDhallToYaml
            (Dhall.JSON.Yaml.defaultOptions)
            "./tasty/data/boolean-quotes"
            True
            False
        , testYamlToDhall
            "./tasty/data/mergify"
        ]

testDhallToYaml :: Options -> String -> Bool -> Bool -> TestTree
testDhallToYaml options prefix testHsYaml testAesonYaml =
    Test.Tasty.testGroup prefix (
        [testCase Dhall.Yaml.dhallToYaml "HsYAML" | testHsYaml] <>
        [testCase Dhall.JSON.Yaml.dhallToYaml "aeson-yaml" | testAesonYaml]
    )
  where
    testCase dhallToYaml s = Test.Tasty.HUnit.testCase s $ do
        let inputFile = prefix <> ".dhall"
        let outputFile = prefix <> ".yaml"

        text <- Data.Text.IO.readFile inputFile

        actualValue <- dhallToYaml options (Just inputFile) text

        expectedValue <- Data.ByteString.readFile outputFile

        let message = "Conversion to YAML did not generate the expected output"

        Test.Tasty.HUnit.assertEqual message expectedValue actualValue

testYamlToDhall :: String -> TestTree
testYamlToDhall prefix =
    Test.Tasty.HUnit.testCase prefix $ do
        let inputFile = prefix <> ".yaml"
        let outputFile = prefix <> ".dhall"

        bytes <- Data.ByteString.readFile inputFile

        expression <- YamlToDhall.dhallFromYaml (YamlToDhall.defaultOptions Nothing) bytes

        let actualValue = Dhall.Core.pretty expression <> "\n"

        expectedValue <- Data.Text.IO.readFile outputFile

        let message =
                "Conversion from YAML did not generate the expected output"

        Test.Tasty.HUnit.assertEqual message expectedValue actualValue
