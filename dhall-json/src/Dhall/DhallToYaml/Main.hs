{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards   #-}

{- Shared code for the @dhall-to-yaml@ and @dhall-to-yaml-ng@ executables
-}
module Dhall.DhallToYaml.Main (main) where

import Control.Applicative (optional, (<|>))
import Control.Exception (SomeException)
import Data.ByteString (ByteString)
import Data.Monoid ((<>))
import Data.Text (Text)
import Dhall.JSON (parsePreservationAndOmission, parseConversion)
import Dhall.JSON.Yaml (Options(..), parseDocuments, parseQuoted)
import Options.Applicative (Parser, ParserInfo)

import qualified Control.Exception
import qualified Data.ByteString
import qualified Data.Text.IO        as Text.IO
import qualified Data.Version
import qualified GHC.IO.Encoding
import qualified Options.Applicative as Options
import qualified System.Exit
import qualified System.IO

parseOptions :: Parser (Maybe Options)
parseOptions =
            Just
        <$> (   Options
            <$> parseExplain
            <*> Dhall.JSON.parsePreservationAndOmission
            <*> parseDocuments
            <*> parseQuoted
            <*> Dhall.JSON.parseConversion
            <*> optional parseFile
            <*> optional parseOutput
            )
    <|> parseVersion
  where
    parseExplain =
        Options.switch
            (   Options.long "explain"
            <>  Options.help "Explain error messages in detail"
            )

    parseFile =
        Options.strOption
            (   Options.long "file"
            <>  Options.help "Read expression from a file instead of standard input"
            <>  Options.metavar "FILE"
            )

    parseVersion =
        Options.flag'
            Nothing
            (   Options.long "version"
            <>  Options.help "Display version"
            )

    parseOutput =
        Options.strOption
            (   Options.long "output"
            <>  Options.help "Write YAML to a file instead of standard output"
            <>  Options.metavar "FILE"
            )

parserInfo :: ParserInfo (Maybe Options)
parserInfo =
    Options.info
        (Options.helper <*> parseOptions)
        (   Options.fullDesc
        <>  Options.progDesc "Compile Dhall to YAML"
        )

main
    :: Data.Version.Version
    -> (Options -> Maybe FilePath -> Text -> IO ByteString)
    -> IO ()
main version = do
    GHC.IO.Encoding.setLocaleEncoding GHC.IO.Encoding.utf8

    maybeOptions <- Options.execParser parserInfo
    mainWith Dhall.Context.empty Nothing version maybeOptions

mainWith
    :: _
    -> Maybe _
    -> Data.Version.Version
    -> (Options -> Maybe FilePath -> Text -> IO ByteString)
    -> Maybe Options
    -> IO ()
mainWith context normalizer version dhallToYaml = \case
    Nothing ->
        putStrLn (Data.Version.showVersion version)

    Just options@(Options {..}) -> do
        handle $ do
            contents <- case file of
                Nothing   -> Text.IO.getContents
                Just path -> Text.IO.readFile path

            let write =
                    case output of
                        Nothing    -> Data.ByteString.putStr
                        Just file_ -> Data.ByteString.writeFile file_

            write =<< dhallToYaml options file contents

handle :: IO a -> IO a
handle = Control.Exception.handle handler
  where
    handler :: SomeException -> IO a
    handler e = do
        System.IO.hPutStrLn System.IO.stderr ""
        System.IO.hPrint    System.IO.stderr e
        System.Exit.exitFailure
