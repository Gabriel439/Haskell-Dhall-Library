module Main where

import           Test.Tasty               (TestTree)

import qualified Dhall.Test.Binary
import qualified Dhall.Test.Format
import qualified Dhall.Test.Import
import qualified Dhall.Test.Lint
import qualified Dhall.Test.Normalization
import qualified Dhall.Test.Parser
import qualified Dhall.Test.QuickCheck
import qualified Dhall.Test.Regression
import qualified Dhall.Test.Tutorial
import qualified Dhall.Test.TypeCheck
import qualified GHC.IO.Encoding
import qualified System.Directory
import qualified System.Environment
import qualified System.IO
import qualified Test.Tasty

import           System.FilePath          ((</>))

allTests :: TestTree
allTests =
    Test.Tasty.testGroup "Dhall Tests"
        [ Dhall.Test.Normalization.tests
        , Dhall.Test.Parser.tests
        , Dhall.Test.Binary.tests
        , Dhall.Test.Regression.tests
        , Dhall.Test.Tutorial.tests
        , Dhall.Test.Format.tests
        , Dhall.Test.TypeCheck.tests
        , Dhall.Test.Import.tests
        , Dhall.Test.QuickCheck.tests
        , Dhall.Test.Lint.tests
        ]

main :: IO ()
main = do

    GHC.IO.Encoding.setLocaleEncoding System.IO.utf8
    pwd <- System.Directory.getCurrentDirectory
    System.Environment.setEnv "XDG_CACHE_HOME" (pwd </> ".cache")
    Test.Tasty.defaultMain allTests
