{-| This module contains the top-level entrypoint and options parsing for the
    @dhall@ executable
-}

{-# LANGUAGE DeriveAnyClass    #-}
{-# LANGUAGE NamedFieldPuns    #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards   #-}

module Dhall.Main
    ( -- * Options
      Options(..)
    , Mode(..)
    , parseOptions
    , parserInfoOptions

      -- * Execution
    , command
    , main
    ) where

import Control.Applicative (optional, (<|>))
import Control.Exception (Exception, SomeException)
import Data.Monoid ((<>))
import Data.Text (Text)
import Data.Text.Prettyprint.Doc (Doc, Pretty)
import Data.Version (showVersion)
import Dhall.Binary (StandardVersion)
import Dhall.Core (Expr(..), Import)
import Dhall.Import (Imported(..))
import Dhall.Parser (Src)
import Dhall.Pretty (Ann, CharacterSet(..), annToAnsiStyle, layoutOpts)
import Dhall.TypeCheck (DetailedTypeError(..), TypeError, X)
import Lens.Family (set)
import Options.Applicative (Parser, ParserInfo)
import System.Exit (exitFailure)
import System.IO (Handle)

import qualified Codec.CBOR.JSON
import qualified Codec.CBOR.Read
import qualified Codec.CBOR.Write
import qualified Codec.Serialise
import qualified Control.Exception
import qualified Control.Monad.Trans.State.Strict          as State
import qualified Data.Aeson
import qualified Data.Aeson.Encode.Pretty
import qualified Data.ByteString.Lazy
import qualified Data.ByteString.Lazy.Char8
import qualified Data.Text
import qualified Data.Text.IO
import qualified Data.Text.Prettyprint.Doc                 as Pretty
import qualified Data.Text.Prettyprint.Doc.Render.Terminal as Pretty
import qualified Dhall
import qualified Dhall.Binary
import qualified Dhall.Core
import qualified Dhall.Diff
import qualified Dhall.Format
import qualified Dhall.Freeze
import qualified Dhall.Hash
import qualified Dhall.Import
import qualified Dhall.Import.Types
import qualified Dhall.Lint
import qualified Dhall.Parser
import qualified Dhall.Pretty
import qualified Dhall.Repl
import qualified Dhall.TypeCheck
import qualified GHC.IO.Encoding
import qualified Options.Applicative
import qualified Paths_dhall as Meta
import qualified System.Console.ANSI
import qualified System.IO
import qualified Text.Dot

-- | Top-level program options
data Options = Options
    { mode            :: Mode
    , explain         :: Bool
    , plain           :: Bool
    , ascii           :: Bool
    , standardVersion :: StandardVersion
    }

-- | The subcommands for the @dhall@ executable
data Mode
    = Default { annotate :: Bool }
    | Version
    | Resolve { dot :: Bool }
    | Type
    | Normalize
    | Repl
    | Format { inplace :: Maybe FilePath }
    | Freeze { inplace :: Maybe FilePath }
    | Hash
    | Diff { expr1 :: Text, expr2 :: Text }
    | Lint { inplace :: Maybe FilePath }
    | Encode { json :: Bool }
    | Decode { json :: Bool }

-- | `Parser` for the `Options` type
parseOptions :: Parser Options
parseOptions =
        Options
    <$> parseMode
    <*> switch "explain" "Explain error messages in more detail"
    <*> switch "plain" "Disable syntax highlighting"
    <*> switch "ascii" "Format code using only ASCII syntax"
    <*> Dhall.Binary.parseStandardVersion
  where
    switch name description =
        Options.Applicative.switch
            (   Options.Applicative.long name
            <>  Options.Applicative.help description
            )

subcommand :: String -> String -> Parser a -> Parser a
subcommand name description parser =
    Options.Applicative.hsubparser
        (   Options.Applicative.command name parserInfo
        <>  Options.Applicative.metavar name
        )
  where
    parserInfo =
        Options.Applicative.info parser
            (   Options.Applicative.fullDesc
            <>  Options.Applicative.progDesc description
            )

parseMode :: Parser Mode
parseMode =
        subcommand
            "version"
            "Display version"
            (pure Version)
    <|> subcommand
            "resolve"
            "Resolve an expression's imports"
            (Resolve <$> parseDot)
    <|> subcommand
            "type"
            "Infer an expression's type"
            (pure Type)
    <|> subcommand
            "normalize"
            "Normalize an expression"
            (pure Normalize)
    <|> subcommand
            "repl"
            "Interpret expressions in a REPL"
            (pure Repl)
    <|> subcommand
            "diff"
            "Render the difference between the normal form of two expressions"
            (Diff <$> argument "expr1" <*> argument "expr2")
    <|> subcommand
            "hash"
            "Compute semantic hashes for Dhall expressions"
            (pure Hash)
    <|> subcommand
            "lint"
            "Improve Dhall code"
            (Lint <$> optional parseInplace)
    <|> subcommand
            "format"
            "Formatter for the Dhall language"
            (Format <$> optional parseInplace)
    <|> subcommand
            "freeze"
            "Add hashes to all import statements of an expression"
            (Freeze <$> optional parseInplace)
    <|> subcommand
            "encode"
            "Encode a Dhall expression to binary"
            (Encode <$> parseJSONFlag)
    <|> subcommand
            "decode"
            "Decode a Dhall expression from binary"
            (Decode <$> parseJSONFlag)
    <|> (Default <$> parseAnnotate)
  where
    argument =
            fmap Data.Text.pack
        .   Options.Applicative.strArgument
        .   Options.Applicative.metavar

    parseAnnotate =
        Options.Applicative.switch
            (Options.Applicative.long "annotate")

    parseDot =
        Options.Applicative.switch
        (   Options.Applicative.long "dot"
        <>  Options.Applicative.help
              "Output import dependency graph in dot format"
        )

    parseInplace =
        Options.Applicative.strOption
        (   Options.Applicative.long "inplace"
        <>  Options.Applicative.help "Modify the specified file in-place"
        <>  Options.Applicative.metavar "FILE"
        )

    parseJSONFlag =
        Options.Applicative.switch
        (   Options.Applicative.long "json"
        <>  Options.Applicative.help "Use JSON representation of CBOR"
        )

throws :: Exception e => Either e a -> IO a
throws (Left  e) = Control.Exception.throwIO e
throws (Right a) = return a

getExpression :: IO (Expr Src Import)
getExpression = do
    inText <- Data.Text.IO.getContents

    throws (Dhall.Parser.exprFromText "(stdin)" inText)

-- | `ParserInfo` for the `Options` type
parserInfoOptions :: ParserInfo Options
parserInfoOptions =
    Options.Applicative.info
        (Options.Applicative.helper <*> parseOptions)
        (   Options.Applicative.progDesc "Interpreter for the Dhall language"
        <>  Options.Applicative.fullDesc
        )

-- | Run the command specified by the `Options` type
command :: Options -> IO ()
command (Options {..}) = do
    let characterSet = case ascii of
            True  -> ASCII
            False -> Unicode

    GHC.IO.Encoding.setLocaleEncoding System.IO.utf8

    let status =
            set Dhall.Import.standardVersion standardVersion (Dhall.Import.emptyStatus ".")


    let handle =
                Control.Exception.handle handler2
            .   Control.Exception.handle handler1
            .   Control.Exception.handle handler0
          where
            handler0 e = do
                let _ = e :: TypeError Src X
                System.IO.hPutStrLn System.IO.stderr ""
                if explain
                    then Control.Exception.throwIO (DetailedTypeError e)
                    else do
                        Data.Text.IO.hPutStrLn System.IO.stderr "\ESC[2mUse \"dhall --explain\" for detailed errors\ESC[0m"
                        Control.Exception.throwIO e

            handler1 (Imported ps e) = do
                let _ = e :: TypeError Src X
                System.IO.hPutStrLn System.IO.stderr ""
                if explain
                    then Control.Exception.throwIO (Imported ps (DetailedTypeError e))
                    else do
                        Data.Text.IO.hPutStrLn System.IO.stderr "\ESC[2mUse \"dhall --explain\" for detailed errors\ESC[0m"
                        Control.Exception.throwIO (Imported ps e)

            handler2 e = do
                let _ = e :: SomeException
                System.IO.hPrint System.IO.stderr e
                System.Exit.exitFailure

    let renderDoc :: Handle -> Doc Ann -> IO ()
        renderDoc h doc = do
            let stream = Pretty.layoutSmart layoutOpts doc

            supportsANSI <- System.Console.ANSI.hSupportsANSI h
            let ansiStream =
                    if supportsANSI && not plain
                    then fmap annToAnsiStyle stream
                    else Pretty.unAnnotateS stream

            Pretty.renderIO h ansiStream
            Data.Text.IO.hPutStrLn h ""

    let render :: Pretty a => Handle -> Expr s a -> IO ()
        render h expression = do
            let doc = Dhall.Pretty.prettyCharacterSet characterSet expression

            renderDoc h doc

    handle $ case mode of
        Version -> do
            putStrLn (showVersion Meta.version)

        Default {..} -> do
            expression <- getExpression

            resolvedExpression <- State.evalStateT (Dhall.Import.loadWith expression) status

            inferredType <- throws (Dhall.TypeCheck.typeOf resolvedExpression)

            let normalizedExpression = Dhall.Core.normalize resolvedExpression

            let annotatedExpression =
                    if annotate
                        then Annot normalizedExpression inferredType
                        else normalizedExpression

            render System.IO.stdout annotatedExpression

        Resolve dot -> do
            expression <- getExpression

            (resolvedExpression, Dhall.Import.Types.Status { _dot }) <-
                State.runStateT (Dhall.Import.loadWith expression) status

            if   dot
            then putStr . ("strict " <>) . Text.Dot.showDot $
                 Text.Dot.attribute ("rankdir", "LR") >> _dot
            else render System.IO.stdout resolvedExpression

        Normalize -> do
            expression <- getExpression

            resolvedExpression <- Dhall.Import.assertNoImports expression

            _ <- throws (Dhall.TypeCheck.typeOf resolvedExpression)

            render System.IO.stdout (Dhall.Core.normalize resolvedExpression)

        Type -> do
            expression <- getExpression

            resolvedExpression <- Dhall.Import.assertNoImports expression

            inferredType <- throws (Dhall.TypeCheck.typeOf resolvedExpression)

            render System.IO.stdout (Dhall.Core.normalize inferredType)

        Repl -> do
            Dhall.Repl.repl characterSet explain standardVersion

        Diff {..} -> do
            expression1 <- Dhall.inputExpr expr1

            expression2 <- Dhall.inputExpr expr2

            let diff = Dhall.Diff.diffNormalized expression1 expression2

            renderDoc System.IO.stdout diff

        Format {..} -> do
            Dhall.Format.format characterSet inplace

        Freeze {..} -> do
            Dhall.Freeze.freeze inplace standardVersion

        Hash -> do
            Dhall.Hash.hash standardVersion

        Lint {..} -> do
            case inplace of
                Just file -> do
                    text <- Data.Text.IO.readFile file

                    (header, expression) <- throws (Dhall.Parser.exprAndHeaderFromText file text)

                    let lintedExpression = Dhall.Lint.lint expression

                    let doc =   Pretty.pretty header
                            <>  Dhall.Pretty.prettyCharacterSet characterSet lintedExpression

                    System.IO.withFile file System.IO.WriteMode (\h -> do
                        renderDoc h doc )

                Nothing -> do
                    text <- Data.Text.IO.getContents

                    (header, expression) <- throws (Dhall.Parser.exprAndHeaderFromText "(stdin)" text)

                    let lintedExpression = Dhall.Lint.lint expression

                    let doc =   Pretty.pretty header
                            <>  Dhall.Pretty.prettyCharacterSet characterSet lintedExpression

                    renderDoc System.IO.stdout doc

        Encode {..} -> do
            expression <- getExpression

            let term = Dhall.Binary.encodeWithVersion standardVersion expression

            let bytes = Codec.Serialise.serialise term

            if json
                then do
                    let decoder = Codec.CBOR.JSON.decodeValue False

                    (_, value) <- throws (Codec.CBOR.Read.deserialiseFromBytes decoder bytes)

                    let jsonBytes = Data.Aeson.Encode.Pretty.encodePretty value

                    Data.ByteString.Lazy.Char8.putStrLn jsonBytes

                else do
                    Data.ByteString.Lazy.putStr bytes

        Decode {..} -> do
            bytes <- Data.ByteString.Lazy.getContents

            term <- do
                if json
                    then do
                        value <- case Data.Aeson.eitherDecode' bytes of
                            Left  string -> fail string
                            Right value  -> return value

                        let encoding = Codec.CBOR.JSON.encodeValue value

                        let cborBytes = Codec.CBOR.Write.toLazyByteString encoding
                        throws (Codec.Serialise.deserialiseOrFail cborBytes)
                    else do
                        throws (Codec.Serialise.deserialiseOrFail bytes)

            expression <- throws (Dhall.Binary.decodeWithVersion term)

            let doc = Dhall.Pretty.prettyCharacterSet characterSet expression

            renderDoc System.IO.stdout doc

-- | Entry point for the @dhall@ executable
main :: IO ()
main = do
    options <- Options.Applicative.execParser parserInfoOptions
    command options
