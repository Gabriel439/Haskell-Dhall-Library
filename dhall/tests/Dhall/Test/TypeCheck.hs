{-# LANGUAGE OverloadedStrings #-}

module Dhall.Test.TypeCheck where

import Data.Monoid (mempty, (<>))
import Data.Text (Text)
import Dhall.Import (Imported)
import Dhall.Parser (Src)
import Dhall.TypeCheck (TypeError, X)
import Test.Tasty (TestTree)

import qualified Control.Exception
import qualified Data.Text
import qualified Dhall.Core
import qualified Dhall.Import
import qualified Dhall.Parser
import qualified Dhall.TypeCheck
import qualified Test.Tasty
import qualified Test.Tasty.HUnit

tests :: TestTree
tests =
    Test.Tasty.testGroup "typecheck tests"
        [ preludeExamples
        , accessTypeChecks
        , should
            "allow type-valued fields in a record"
            "success/simple/fieldsAreTypes"
        , should
            "allow type-valued alternatives in a union"
            "success/simple/alternativesAreTypes"
        , should
            "allow anonymous functions in types to be judgmentally equal"
            "success/simple/anonymousFunctionsInTypes"
        , should
            "correctly handle α-equivalent merge alternatives"
            "success/simple/mergeEquivalence"
        , should
            "allow Kind variables"
            "success/simple/kindParameter"
        , shouldNotTypeCheck
            "combining records of terms and types"
            "failure/combineMixedRecords"
        , shouldNotTypeCheck
            "preferring a record of types over a record of terms"
            "failure/preferMixedRecords"
        , should
            "allow records of types of mixed kinds"
            "success/recordOfTypes"
        , should
            "allow accessing a type from a record"
            "success/accessType"
        , should
            "allow accessing a type from a Boehm-Berarducci-encoded record"
            "success/accessEncodedType"
        , shouldNotTypeCheck
            "Hurkens' paradox"
            "failure/hurkensParadox"
        , should
            "allow accessing a constructor from a type stored inside a record"
            "success/simple/mixedFieldAccess"
        , should
            "allow a record of a record of types"
            "success/recordOfRecordOfTypes"
        ]

preludeExamples :: TestTree
preludeExamples =
    Test.Tasty.testGroup "Prelude examples"
        [ should "Monoid" "./success/prelude/Monoid/00"
        , should "Monoid" "./success/prelude/Monoid/01"
        , should "Monoid" "./success/prelude/Monoid/02"
        , should "Monoid" "./success/prelude/Monoid/03"
        , should "Monoid" "./success/prelude/Monoid/04"
        , should "Monoid" "./success/prelude/Monoid/05"
        , should "Monoid" "./success/prelude/Monoid/06"
        , should "Monoid" "./success/prelude/Monoid/07"
        , should "Monoid" "./success/prelude/Monoid/08"
        , should "Monoid" "./success/prelude/Monoid/09"
        , should "Monoid" "./success/prelude/Monoid/10"
        ]

accessTypeChecks :: TestTree
accessTypeChecks =
    Test.Tasty.testGroup "typecheck access"
        [ should "record" "./success/simple/access/0"
        , should "record" "./success/simple/access/1"
        ]

should :: Text -> Text -> TestTree
should name basename =
    Test.Tasty.HUnit.testCase (Data.Text.unpack name) $ do
        let actualCode   = "./tests/typecheck/" <> basename <> "A.dhall"
        let expectedCode = "./tests/typecheck/" <> basename <> "B.dhall"

        actualExpr <- case Dhall.Parser.exprFromText mempty actualCode of
            Left  err  -> Control.Exception.throwIO err
            Right expr -> return expr
        expectedExpr <- case Dhall.Parser.exprFromText mempty expectedCode of
            Left  err  -> Control.Exception.throwIO err
            Right expr -> return expr

        let annotatedExpr = Dhall.Core.Annot actualExpr expectedExpr

        resolvedExpr <- Dhall.Import.load annotatedExpr
        case Dhall.TypeCheck.typeOf resolvedExpr of
            Left  err -> Control.Exception.throwIO err
            Right _   -> return ()

shouldNotTypeCheck :: Text -> Text -> TestTree
shouldNotTypeCheck name basename =
    Test.Tasty.HUnit.testCase (Data.Text.unpack name) $ do
        let code = "./tests/typecheck/" <> basename <> ".dhall"

        expression <- case Dhall.Parser.exprFromText mempty code of
            Left  exception  -> Control.Exception.throwIO exception
            Right expression -> return expression

        let io :: IO Bool
            io = do
                _ <- Dhall.Import.load expression
                return True

        let handler :: Imported (TypeError Src X)-> IO Bool
            handler _ = return False

        typeChecked <- Control.Exception.handle handler io

        if typeChecked
            then fail (Data.Text.unpack code <> " should not have type-checked")
            else return ()
