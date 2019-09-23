{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE RecordWildCards     #-}
{-# LANGUAGE PatternGuards       #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE FlexibleInstances   #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Main where

import Control.Applicative (optional, (<|>))
import Control.Exception (SomeException, throwIO)
import Data.Monoid ((<>))
import Data.Text (Text)
import Data.Version (showVersion)
import Dhall.JSONToDhall
import Dhall.Pretty (CharacterSet(..))
import Options.Applicative (Parser, ParserInfo)

import qualified Control.Exception
import qualified Data.Aeson                                as Aeson
import qualified Data.ByteString.Lazy.Char8                as ByteString
import qualified Data.Text.IO                              as Text.IO
import qualified Data.Text.Prettyprint.Doc                 as Pretty
import qualified Data.Text.Prettyprint.Doc.Render.Terminal as Pretty.Terminal
import qualified Data.Text.Prettyprint.Doc.Render.Text     as Pretty.Text
import qualified GHC.IO.Encoding
import qualified Options.Applicative                       as Options
import qualified System.Console.ANSI                       as ANSI
import qualified System.Exit
import qualified System.IO                                 as IO
import qualified Dhall.Pretty
import qualified Paths_dhall_json                          as Meta

-- ---------------
-- Command options
-- ---------------

-- | Command info and description
parserInfo :: ParserInfo Options
parserInfo = Options.info
          (  Options.helper <*> parseOptions)
          (  Options.fullDesc
          <> Options.progDesc "Convert a JSON expression to a Dhall expression, given the expected Dhall type"
          )

-- | All the command arguments and options
data Options
    = Options
        { schema     :: Text
        , conversion :: Conversion
        , file       :: Maybe FilePath
        , output     :: Maybe FilePath
        , ascii      :: Bool
        , plain      :: Bool
        }
    | Version
    deriving Show

-- | Parser for all the command arguments and options
parseOptions :: Parser Options
parseOptions =
        (   Options
        <$> parseSchema
        <*> parseConversion
        <*> optional parseFile
        <*> optional parseOutput
        <*> parseASCII
        <*> parsePlain
        )
    <|> parseVersion
  where
    parseSchema =
        Options.strArgument
            (  Options.metavar "SCHEMA"
            <> Options.help "Dhall type expression (schema)"
            )

    parseVersion =
        Options.flag'
            Version
            (  Options.long "version"
            <> Options.short 'V'
            <> Options.help "Display version"
            )

    parseFile =
        Options.strOption
            (   Options.long "file"
            <>  Options.help "Read JSON from a file instead of standard input"
            <>  Options.metavar "FILE"
            )

    parseOutput =
        Options.strOption
            (   Options.long "output"
            <>  Options.help "Write Dhall expression to a file instead of standard output"
            <>  Options.metavar "FILE"
            )

    parseASCII =
        Options.switch
            (   Options.long "ascii"
            <>  Options.help "Format code using only ASCII syntax"
            )

    parsePlain =
        Options.switch
            (   Options.long "plain"
            <>  Options.help "Disable syntax highlighting"
            )

-- ----------
-- Main
-- ----------

main :: IO ()
main = do
    GHC.IO.Encoding.setLocaleEncoding GHC.IO.Encoding.utf8

    options <- Options.execParser parserInfo

    case options of
        Version -> do
            putStrLn (showVersion Meta.version)

        Options {..} -> do
            let characterSet = case ascii of
                    True  -> ASCII
                    False -> Unicode

            handle $ do
                bytes <- case file of
                    Nothing   -> ByteString.getContents
                    Just path -> ByteString.readFile path

                value :: Aeson.Value <- case Aeson.eitherDecode bytes of
                  Left err -> throwIO (userError err)
                  Right v -> pure v

                expr <- typeCheckSchemaExpr id =<< resolveSchemaExpr schema

                result <- case dhallFromJSON conversion expr value of
                  Left err     -> throwIO err
                  Right result -> return result

                let document = Dhall.Pretty.prettyCharacterSet characterSet result

                let stream = Pretty.layoutSmart Dhall.Pretty.layoutOpts document

                case output of
                    Nothing -> do
                        supportsANSI <- ANSI.hSupportsANSI IO.stdout

                        let ansiStream =
                                if supportsANSI && not plain
                                then fmap Dhall.Pretty.annToAnsiStyle stream
                                else Pretty.unAnnotateS stream

                        Pretty.Terminal.renderIO IO.stdout ansiStream

                        Text.IO.putStrLn ""

                    Just file_ ->
                        IO.withFile file_ IO.WriteMode $ \h -> do
                            Pretty.Text.renderIO h stream

                            Text.IO.hPutStrLn h ""

handle :: IO a -> IO a
handle = Control.Exception.handle handler
  where
    handler :: SomeException -> IO a
    handler e = do
        IO.hPutStrLn IO.stderr ""
        IO.hPrint    IO.stderr e
        System.Exit.exitFailure
