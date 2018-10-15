{-# LANGUAGE OverloadedStrings #-}

module Parser where

import Data.Text (Text)
import Test.Tasty (TestTree)

import qualified Control.Exception
import qualified Data.Text
import qualified Data.Text.IO
import qualified Dhall.Parser
import qualified Test.Tasty
import qualified Test.Tasty.HUnit

parserTests :: TestTree
parserTests =
    Test.Tasty.testGroup "parser tests"
        [ Test.Tasty.testGroup "whitespace"
            [ shouldParse
                "prefix/suffix"
                "./tests/parser/whitespace.dhall"
            , shouldParse
                "block comment"
                "./tests/parser/blockComment.dhall"
            , shouldParse
                "nested block comment"
                "./tests/parser/nestedBlockComment.dhall"
            , shouldParse
                "line comment"
                "./tests/parser/lineComment.dhall"
            , shouldParse
                "Unicode comment"
                "./tests/parser/unicodeComment.dhall"
            , shouldParse
                "whitespace buffet"
                "./tests/parser/whitespaceBuffet.dhall"
            ]
        , shouldParse
            "label"
            "./tests/parser/label.dhall"
        , shouldParse
            "quoted label"
            "./tests/parser/quotedLabel.dhall"
        , shouldParse
            "double quoted string"
            "./tests/parser/doubleQuotedString.dhall"
        , shouldParse
            "Unicode double quoted string"
            "./tests/parser/unicodeDoubleQuotedString.dhall"
        , shouldParse
            "escaped double quoted string"
            "./tests/parser/escapedDoubleQuotedString.dhall"
        , shouldParse
            "interpolated double quoted string"
            "./tests/parser/interpolatedDoubleQuotedString.dhall"
        , shouldParse
            "single quoted string"
            "./tests/parser/singleQuotedString.dhall"
        , shouldParse
            "escaped single quoted string"
            "./tests/parser/escapedSingleQuotedString.dhall"
        , shouldParse
            "interpolated single quoted string"
            "./tests/parser/interpolatedSingleQuotedString.dhall"
        , shouldParse
            "double"
            "./tests/parser/double.dhall"
        , shouldParse
            "natural"
            "./tests/parser/natural.dhall"
        , shouldParse
            "identifier"
            "./tests/parser/identifier.dhall"
        , shouldParse
            "paths"
            "./tests/parser/paths.dhall"
        , shouldParse
            "path termination"
            "./tests/parser/pathTermination.dhall"
        , shouldParse
            "urls"
            "./tests/parser/urls.dhall"
        , shouldParse
            "environmentVariables"
            "./tests/parser/environmentVariables.dhall"
        , shouldParse
            "lambda"
            "./tests/parser/lambda.dhall"
        , shouldParse
            "if then else"
            "./tests/parser/ifThenElse.dhall"
        , shouldParse
            "let"
            "./tests/parser/let.dhall"
        , shouldParse
            "forall"
            "./tests/parser/forall.dhall"
        , shouldParse
            "function type"
            "./tests/parser/functionType.dhall"
        , shouldParse
            "operators"
            "./tests/parser/operators.dhall"
        , shouldParse
            "annotations"
            "./tests/parser/annotations.dhall"
        , shouldParse
            "merge"
            "./tests/parser/merge.dhall"
        , shouldParse
            "constructors"
            "./tests/parser/constructors.dhall"
        , shouldParse
            "fields"
            "./tests/parser/fields.dhall"
        , shouldParse
            "record"
            "./tests/parser/record.dhall"
        , shouldParse
            "union"
            "./tests/parser/union.dhall"
        , shouldParse
            "list"
            "./tests/parser/list.dhall"
        , shouldParse
            "builtins"
            "./tests/parser/builtins.dhall"
        , shouldParse
            "import alternatives"
            "./tests/parser/importAlt.dhall"
        , shouldParse
            "large expression"
            "./tests/parser/largeExpression.dhall"
        , shouldParse
            "names that begin with reserved identifiers"
            "./tests/parser/reservedPrefix.dhall"
        , shouldParse
            "interpolated expressions with leading whitespace"
            "./tests/parser/template.dhall"
        , shouldNotParse
            "records with duplicate fields"
            "./tests/parser/failure/duplicateFields.dhall"
        , shouldParse
            "collections with type annotations containing imports"
            "./tests/parser/collectionImportType.dhall"
        , shouldParse
            "a parenthesized custom header import"
            "./tests/parser/parenthesizeUsing.dhall"
        , shouldNotParse
            "accessing a field of an import without parentheses"
            "./tests/parser/failure/importAccess.dhall"
        , shouldParse
            "Sort"
            "./tests/parser/sort.dhall"
        ]

shouldParse :: Text -> FilePath -> TestTree
shouldParse name path = Test.Tasty.HUnit.testCase (Data.Text.unpack name) (do
    text <- Data.Text.IO.readFile path
    case Dhall.Parser.exprFromText mempty text of
        Left err -> Control.Exception.throwIO err
        Right _  -> return () )

shouldNotParse :: Text -> FilePath -> TestTree
shouldNotParse name path = Test.Tasty.HUnit.testCase (Data.Text.unpack name) (do
    text <- Data.Text.IO.readFile path
    case Dhall.Parser.exprFromText mempty text of
        Left  _ -> return ()
        Right _ -> fail "Unexpected successful parser" )
