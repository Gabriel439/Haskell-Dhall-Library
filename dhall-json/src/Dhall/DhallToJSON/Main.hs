{-# LANGUAGE RecordWildCards   #-}
{-# LANGUAGE OverloadedStrings #-}

module Dhall.DhallToJSON.Main
    ( Options (..)
    , parseOptions
    , parserInfo
    , main
    , mainWith
    ) where

import Control.Applicative ((<|>), optional)
import Control.Exception (SomeException)
import Data.Aeson (Value)
import Data.Monoid ((<>))
import Dhall.JSON (Conversion, SpecialDoubleMode(..))
import Options.Applicative (Parser, ParserInfo)

import qualified Control.Exception
import qualified Data.Aeson
import qualified Data.Data.Aeson.Encode.Pretty as Data.Aeson.Pretty
import qualified Data.ByteString.Lazy
import qualified Data.Text.IO                  as Text.IO
import qualified Data.Version
import qualified Dhall
import qualified Dhall.Context
import qualified Dhall.JSON
import qualified GHC.IO.Encoding
import qualified Options.Applicative           as Options
import qualified Paths_dhall_json              as Meta
import qualified System.Exit
import qualified System.IO

data Options
    = Options
        { explain                   :: Bool
        , pretty                    :: Bool
        , omission                  :: Value -> Value
        , conversion                :: Conversion
        , approximateSpecialDoubles :: Bool
        , file                      :: Maybe FilePath
        , output                    :: Maybe FilePath
        }
    | Version

parseOptions :: Parser Options
parseOptions =
        (   Options
        <$> parseExplain
        <*> parsePretty
        <*> Dhall.JSON.parsePreservationAndOmission
        <*> Dhall.JSON.parseConversion
        <*> parseApproximateSpecialDoubles
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

    parsePretty =
        prettyFlag <|> compactFlag <|> defaultBehavior
      where
        prettyFlag =
            Options.flag'
                True
                (   Options.long "pretty"
                <>  Options.help "Deprecated, will be removed soon. Pretty print generated JSON"
                )

        compactFlag =
            Options.flag'
                False
                (   Options.long "compact"
                <>  Options.help "Render JSON on one line"
                )

        defaultBehavior =
            pure True

    parseVersion =
        Options.flag'
            Version
            (   Options.long "version"
            <>  Options.help "Display version"
            )

    parseApproximateSpecialDoubles =
        Options.switch
            (   Options.long "approximate-special-doubles"
            <>  Options.help "Use approximate representation for NaN/±Infinity"
            )

    parseFile =
        Options.strOption
            (   Options.long "file"
            <>  Options.help "Read expression from a file instead of standard input"
            <>  Options.metavar "FILE"
            )

    parseOutput =
        Options.strOption
            (   Options.long "output"
            <>  Options.help "Write JSON to a file instead of standard output"
            <>  Options.metavar "FILE"
            )

parserInfo :: ParserInfo Options
parserInfo =
    Options.info
        (Options.helper <*> parseOptions)
        (   Options.fullDesc
        <>  Options.progDesc "Compile Dhall to JSON"
        )

main
    :: Data.Version.Version
    -> IO ()
main version = do
    GHC.IO.Encoding.setLocaleEncoding GHC.IO.Encoding.utf8

    options <- Options.execParser parserInfo
    mainWith Dhall.Context.empty Nothing options

mainWith
    :: _
    -> Maybe _
    -> Data.Version.Version
    -> Options
    -> IO ()
mainWith context normalizer version = \case
    Version ->
        putStrLn (Data.Version.showVersion version)

    Options {..} -> do
        handle $ do
            let config = Data.Aeson.Pretty.Config
                        { Data.Aeson.Pretty.confIndent          = Data.Aeson.Pretty.Spaces 2
                        , Data.Aeson.Pretty.confCompare         = compare
                        , Data.Aeson.Pretty.confNumFormat       = Data.Aeson.Pretty.Generic
                        , Data.Aeson.Pretty.confTrailingNewline = False
                        }

            let encode =
                    if pretty
                        then Data.Aeson.Pretty.encodePretty' config
                        else Data.Aeson.encode

            let explaining =
                    if explain
                        then Dhall.detailed
                        else id

            let doubleMode =
                    if approximateSpecialDoubles
                        then ApproximateWithinJSON
                        else ForbidWithinJSON

            let write =
                    case output of
                        Nothing    -> Data.ByteString.Lazy.putStr
                        Just file_ -> Data.ByteString.Lazy.writeFile file_

            text <- case file of
                Nothing   -> Text.IO.getContents
                Just path -> Text.IO.readFile path

            json <-
                explaining
                    (Dhall.JSON.codeToValueWith context normalizer conversion doubleMode file text)

            write (encode (omission json) <> "\n")

handle :: IO a -> IO a
handle = Control.Exception.handle handler
  where
    handler :: SomeException -> IO a
    handler e = do
        System.IO.hPutStrLn System.IO.stderr ""
        System.IO.hPrint    System.IO.stderr e
        System.Exit.exitFailure
