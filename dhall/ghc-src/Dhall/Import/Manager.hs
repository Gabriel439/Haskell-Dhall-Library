{-# LANGUAGE CPP #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE RecordWildCards #-}

{-| Both the GHC and GHCJS implementations of 'Dhall.Import.Manager.Manager'
    export a `Dhall.Import.Manager.Manager` type suitable for use within the
    "Dhall.Import" module

    For the GHC implementation the `Dhall.Import.Manager` type is a real
    `Network.HTTP.Client.Manager` from the @http-client@ package.  For the
    GHCJS implementation the `Dhall.Import.Manager.Manager` type is
    a synonym for @`Data.Void.Void`@ since GHCJS does not use a
    `Network.HTTP.Client.Manager` for HTTP requests.
-}
module Dhall.Import.Manager
    ( -- * Manager
      Manager(..)
    , defaultNewManager
    ) where

import qualified Network.HTTP.Client as Client
import qualified Network.HTTP.Client as HTTP
import Dhall.Import.UserHeaders (UserHeaders, defaultNewUserHeaders)

#ifdef USE_HTTP_CLIENT_TLS
import Network.HTTP.Client.TLS (tlsManagerSettings)
#endif

data Manager = Manager { httpManager :: Client.Manager, headersManager :: UserHeaders }

defaultNewManager :: IO Manager
defaultNewManager =
  build <$> (Client.newManager
#ifdef USE_HTTP_CLIENT_TLS
    tlsManagerSettings
#else
    HTTP.defaultManagerSettings
#endif
    { HTTP.managerResponseTimeout = HTTP.responseTimeoutMicro (30 * 1000 * 1000) }  -- 30 seconds
  ) where
    build httpManager = Manager { httpManager, headersManager = defaultNewUserHeaders }