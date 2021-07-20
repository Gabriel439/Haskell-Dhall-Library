{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards   #-}
{-# LANGUAGE NamedFieldPuns    #-}

module Dhall.Import.HTTP
    ( fetchFromHttpUrl
    ) where

import Control.Exception                (Exception)
import Control.Monad.IO.Class           (MonadIO (..))
import Control.Monad.Trans.State.Strict (StateT)
import Data.ByteString                  (ByteString)
import Data.CaseInsensitive             (CI)
import Data.Dynamic                     (toDyn)
import Data.List.NonEmpty               (NonEmpty(..))
import Dhall.Core
    ( Import (..)
    , ImportHashed (..)
    , ImportType (..)
    , Scheme (..)
    , URL (..)
    )
import Dhall.Import.Types hiding (Manager)
import Dhall.Import.Manager (Manager(..))
import Dhall.Import.UserHeaders (withUserHeaders)
import Dhall.URL                        (renderURL)


import Network.HTTP.Client
    ( HttpException (..)
    , HttpExceptionContent (..)
    )

import qualified Control.Exception
import qualified Control.Monad.Trans.State.Strict as State
import qualified Data.Text                        as Text
import qualified Data.Text.Encoding
import qualified Data.Text.Lazy
import qualified Data.Text.Lazy.Encoding
import qualified Dhall.Util
import qualified Network.HTTP.Client              as HTTP
import qualified Network.HTTP.Types

mkPrettyHttpException :: String -> HttpException -> PrettyHttpException
mkPrettyHttpException url ex =
    PrettyHttpException (renderPrettyHttpException url ex) (toDyn ex)

renderPrettyHttpException :: String -> HttpException -> String
renderPrettyHttpException _ (InvalidUrlException _ r) =
      "\n"
  <>  "\ESC[1;31mError\ESC[0m: Invalid URL\n"
  <>  "\n"
  <>  "URL: " <> show r <> "\n"
renderPrettyHttpException url (HttpExceptionRequest _ e) =
  case e of
    ConnectionFailure _ ->
          "\n"
      <>  "\ESC[1;31mError\ESC[0m: Remote host not found\n"
      <>  "\n"
      <>  "URL: " <> url <> "\n"
    InvalidDestinationHost host ->
          "\n"
      <>  "\ESC[1;31mError\ESC[0m: Invalid remote host name:\n"
      <>  "\n"
      <>  "Host: " <> show host <> "\n"
    ResponseTimeout ->
          "\n"
      <>  "\ESC[1;31mError\ESC[0m: The remote host took too long to respond\n"
      <>  "\n"
      <>  "URL: " <> url <> "\n"
    ConnectionTimeout ->
          "\n"
      <>  "\ESC[1;31mError\ESC[0m: Connection establishment took too long\n"
      <>  "\n"
      <>  "URL: " <> url <> "\n"
    StatusCodeException response body -> prefix <> suffix
      where
        prefix
            | statusCode == 401 =
                    "\n"
                <>  "\ESC[1;31mError\ESC[0m: Access unauthorized\n"
            | statusCode == 403 =
                    "\n"
                <>  "\ESC[1;31mError\ESC[0m: Access forbidden\n"
            | statusCode == 404 =
                    "\n"
                <>  "\ESC[1;31mError\ESC[0m: Remote file not found\n"
            | statusCode == 500 =
                    "\n"
                <>  "\ESC[1;31mError\ESC[0m: Server-side failure\n"
            | statusCode == 502 =
                    "\n"
                <>  "\ESC[1;31mError\ESC[0m: Upstream failure\n"
            | statusCode == 503 =
                    "\n"
                <>  "\ESC[1;31mError\ESC[0m: Server temporarily unavailable\n"
            | statusCode == 504 =
                    "\n"
                <>  "\ESC[1;31mError\ESC[0m: Upstream timeout\n"
            | otherwise =
                    "\n"
                <>  "\ESC[1;31mError\ESC[0m: HTTP request failure\n"

        suffix =
                "\n"
            <>  "HTTP status code: " <> show statusCode <> "\n"
            <>  "\n"
            <>  "URL: " <> url <> "\n"
            <>  message

        statusCode =
            Network.HTTP.Types.statusCode
                (HTTP.responseStatus response)

        message =
            case Data.Text.Encoding.decodeUtf8' body of
                Left _ ->
                        "\n"
                    <>  "Message (non-UTF8 bytes):\n"
                    <>  "\n"
                    <>  truncatedBodyString <> "\n"
                  where
                    bodyString = show body

                    dots = "…"

                    truncatedLength = 80 - length dots

                    truncatedBodyString
                        | truncatedLength < length bodyString =
                            take truncatedLength bodyString <> dots
                        | otherwise =
                            bodyString
                Right "" ->
                    ""
                Right bodyText ->
                        "\n"
                    <>  "Message:\n"
                    <>  "\n"
                    <>  Text.unpack prefixedText
                  where
                    prefixedLines =
                        zipWith combine prefixes (Text.lines bodyText)
                      where
                        prefixes =
                            map (Text.pack . show) [(1 ::Int)..7] ++ [ "…" ]

                        combine n line = n <> "│ " <> line

                    prefixedText = Text.unlines prefixedLines

    e' -> "\n"
      <>  "\ESC[1;31mError\ESC[0m: " <> show e'
      <>  "\n"
      <>  "URL: " <> url <> "\n"

newManager :: StateT Status IO Manager
newManager = do
    Status { _manager = oldManager, ..} <- State.get

    case oldManager of
        Nothing -> do
            manager <- liftIO _newManager

            State.put (Status { _manager = Just manager , ..})

            return manager

        Just manager ->
            return manager

data NotCORSCompliant = NotCORSCompliant
    { expectedOrigins :: [ByteString]
    , actualOrigin    :: ByteString
    }

instance Exception NotCORSCompliant

instance Show NotCORSCompliant where
    show (NotCORSCompliant {..}) =
            Dhall.Util._ERROR <> ": Not CORS compliant\n"
        <>  "\n"
        <>  "Dhall supports transitive imports, meaning that an imported expression can\n"
        <>  "import other expressions.  However, a remote import (the \"parent\" import)\n"
        <>  "cannot import another remote import (the \"child\" import) unless the child\n"
        <>  "import grants permission to do using CORS.  The child import must respond with\n"
        <>  "an `Access-Control-Allow-Origin` response header that matches the parent\n"
        <>  "import, otherwise Dhall rejects the import.\n"
        <>  "\n" <> prologue
      where
        prologue =
            case expectedOrigins of
                [ expectedOrigin ] ->
                        "The following parent import:\n"
                    <>  "\n"
                    <>  "↳ " <> show actualOrigin <> "\n"
                    <>  "\n"
                    <>  "... did not match the expected origin:\n"
                    <>  "\n"
                    <>  "↳ " <> show expectedOrigin <> "\n"
                    <>  "\n"
                    <>  "... so import resolution failed.\n"
                [] ->
                        "The child response did not include any `Access-Control-Allow-Origin` header,\n"
                    <>  "so import resolution failed.\n"
                _:_:_ ->
                        "The child response included more than one `Access-Control-Allow-Origin` header,\n"
                    <>  "when only one such header should have been present, so import resolution\n"
                    <>  "failed.\n"
                    <>  "\n"
                    <>  "This may indicate that the server for the child import is misconfigured.\n"

corsCompliant
    :: MonadIO io
    => ImportType -> URL -> [(CI ByteString, ByteString)] -> io ()
corsCompliant (Remote parentURL) childURL responseHeaders = liftIO $ do
    let toOrigin (URL {..}) =
            Data.Text.Encoding.encodeUtf8 (prefix <> "://" <> authority)
          where
            prefix =
                case scheme of
                    HTTP  -> "http"
                    HTTPS -> "https"

    let actualOrigin = toOrigin parentURL

    let childOrigin = toOrigin childURL

    let predicate (header, _) = header == "Access-Control-Allow-Origin"

    let originHeaders = filter predicate responseHeaders

    let expectedOrigins = map snd originHeaders

    case expectedOrigins of
        [expectedOrigin]
            | expectedOrigin == "*" ->
                return ()
            | expectedOrigin == actualOrigin ->
                return ()
        _   | actualOrigin == childOrigin ->
                return ()
            | otherwise ->
                Control.Exception.throwIO (NotCORSCompliant {..})
corsCompliant _ _ _ = return ()

type HTTPHeader = Network.HTTP.Types.Header

fetchFromHttpUrl :: URL -> Maybe [HTTPHeader] -> StateT Status IO Text.Text
fetchFromHttpUrl childURL mheaders = do
    Manager { httpManager, headersManager } <- newManager

    let childURLString = Text.unpack (renderURL childURL)

    request <- liftIO (HTTP.parseUrlThrow childURLString)

    let baseRequest =
            case mheaders of
              Nothing      -> request
              Just headers -> request { HTTP.requestHeaders = headers }

    requestWithHeaders <- liftIO (withUserHeaders headersManager baseRequest)

    let io = HTTP.httpLbs requestWithHeaders httpManager

    let handler e = do
            let _ = e :: HttpException
            Control.Exception.throwIO (mkPrettyHttpException childURLString e)

    response <- liftIO (Control.Exception.handle handler io)

    Status {..} <- State.get

    case _stack of
        -- We ignore the first import in the stack since that is the same import
        -- as the `childUrl`
        _ :| Chained parentImport : _ -> do
            let parentImportType = importType (importHashed parentImport)

            corsCompliant parentImportType childURL (HTTP.responseHeaders response)
        _ -> do
            return ()

    let bytes = HTTP.responseBody response

    case Data.Text.Lazy.Encoding.decodeUtf8' bytes of
        Left  err  -> liftIO (Control.Exception.throwIO err)
        Right text -> return (Data.Text.Lazy.toStrict text)
