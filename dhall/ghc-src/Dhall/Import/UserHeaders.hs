{-# LANGUAGE LambdaCase           #-}
{-# LANGUAGE OverloadedStrings    #-}

module Dhall.Import.UserHeaders
    (
      UserHeaders
    , Headers
    , defaultNewUserHeaders
    , withUserHeaders
    ) where

import Data.Aeson (eitherDecodeStrict')
import Data.HashMap.Strict (HashMap)
import Data.Text (Text)
import Data.Text.Encoding (encodeUtf8, decodeUtf8)
import Network.HTTP.Types (Header)
import System.Directory (getXdgDirectory, XdgDirectory(XdgConfig))
import System.Environment (lookupEnv)
import System.FilePath ((</>))
import Data.Either.Combinators (rightToMaybe)
import Control.Exception (tryJust)
import Control.Monad (guard)
import System.IO.Error (isDoesNotExistError)
import qualified Data.ByteString as B
import qualified Data.CaseInsensitive as CI
import qualified Data.HashMap.Strict  as HashMap
import qualified Data.Text as Text
import qualified Network.HTTP.Client as HTTP

-- todo StateT?
type UserHeaders = ()

type Headers = [Header]

defaultNewUserHeaders :: UserHeaders
defaultNewUserHeaders = ()

loadAllHeaders :: IO (HashMap.HashMap Text Headers)
-- TODO load dhall, not JSON...
loadAllHeaders = getExpr >>= \case
  Just expr -> case eitherDecodeStrict' expr of
    Left err -> fail err
    Right result -> pure $ convert $ result
  Nothing -> pure HashMap.empty
  where
    convert :: HashMap.HashMap Text (HashMap.HashMap Text Text) -> HashMap Text Headers
    convert = HashMap.map toHeaders

    toHeaders :: HashMap.HashMap Text Text -> Headers
    toHeaders hmap = map toHeader (HashMap.toList hmap)

    toHeader :: (Text, Text) -> Header
    toHeader (k, v) = (CI.mk (encodeUtf8 k), encodeUtf8 v)

    getExpr :: IO (Maybe B.ByteString)
    getExpr = lookupEnv "DHALL_HEADERS" >>= \case
      Just expr -> pure $ Just $ encodeUtf8 $ Text.pack expr
      Nothing -> loadConfigFile

    configSuffix = "dhall" </> "headers.dhall"
    loadConfigFile = getXdgDirectory XdgConfig configSuffix >>= tryReadFile

    tryReadFile path = rightToMaybe <$>
      tryJust (guard . isDoesNotExistError) (B.readFile path)

addUserHeaders :: HTTP.Request -> HashMap Text Headers -> HTTP.Request
addUserHeaders request config = addHeaders $ HashMap.lookupDefault [] origin config where
  origin = decodeUtf8 (HTTP.host request) <> ":" <> Text.pack (show (HTTP.port request))

  -- TODO how should we combine user / explicit headers?
  -- I think for forwards compat we should override mheaders (if any)
  -- with userHeaders.
  -- TODO check how library deals with multiple conflicting headers
  -- in the list
  addHeaders newHeaders = request {
    HTTP.requestHeaders = (HTTP.requestHeaders request) <> newHeaders
  }

-- TODO make this lazy / load only once (see ./HTTP newManager)
withUserHeaders :: UserHeaders -> HTTP.Request -> IO HTTP.Request
withUserHeaders () request = addUserHeaders request <$> loadAllHeaders