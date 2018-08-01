{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards   #-}
{-# OPTIONS_GHC -Wall #-}

module Dhall.Import.Types where

import Control.Exception (Exception)
import Control.Monad.Trans.State.Strict (StateT)
import Data.Dynamic
import Data.List.NonEmpty (NonEmpty)
import Data.Map (Map)
import Data.Semigroup ((<>))
import Dhall.Binary (ProtocolVersion(..))
import Dhall.Context (Context)
import Dhall.Core
  ( Directory (..)
  , Expr
  , File (..)
  , FilePrefix (..)
  , Import (..)
  , ImportHashed (..)
  , ImportMode (..)
  , ImportType (..)
  , ReifiedNormalizer(..)
  )
import Dhall.Parser (Src)
import Dhall.TypeCheck (X)
import Lens.Family (LensLike')
import System.FilePath (isRelative, splitDirectories)

import qualified Dhall.Context
import qualified Data.Map      as Map
import qualified Data.Text

-- | State threaded throughout the import process
data Status m = Status
    { _stack :: NonEmpty Import
    -- ^ Stack of `Import`s that we've imported along the way to get to the
    -- current point

    , _cache :: Map Import (Expr Src X)
    -- ^ Cache of imported expressions in order to avoid importing the same
    --   expression twice with different values

    , _manager :: Maybe Dynamic
    -- ^ Cache for the HTTP `Manager` so that we only acquire it once

    , _protocolVersion :: ProtocolVersion

    , _normalizer :: ReifiedNormalizer X

    , _startingContext :: Context (Expr Src X)

    , _resolver :: Import -> StateT (Status m) m (Expr Src Import)
    }

-- | Default starting `Status` that is polymorphic in the base `Monad`
emptyStatusWith
    :: (Import -> StateT (Status m) m (Expr Src Import))
    -> FilePath
    -> Status m
emptyStatusWith _resolver rootDirectory = Status {..}
  where
    _stack = pure rootImport

    _cache = Map.empty

    _manager = Nothing

    _protocolVersion = V_1_0

    _normalizer = ReifiedNormalizer (const Nothing)

    _startingContext = Dhall.Context.empty

    prefix = if isRelative rootDirectory
      then Here
      else Absolute
    pathComponents =
        fmap Data.Text.pack (reverse (splitDirectories rootDirectory))

    dirAsFile = File (Directory pathComponents) "."

    -- Fake import to set the directory we're relative to.
    rootImport = Import
      { importHashed = ImportHashed
        { hash = Nothing
        , importType = Local prefix dirAsFile
        }
      , importMode = Code
      }

stack :: Functor f => LensLike' f (Status m) (NonEmpty Import)
stack k s = fmap (\x -> s { _stack = x }) (k (_stack s))

cache :: Functor f => LensLike' f (Status m) (Map Import (Expr Src X))
cache k s = fmap (\x -> s { _cache = x }) (k (_cache s))

manager :: Functor f => LensLike' f (Status m) (Maybe Dynamic)
manager k s = fmap (\x -> s { _manager = x }) (k (_manager s))

protocolVersion :: Functor f => LensLike' f (Status m) ProtocolVersion
protocolVersion k s =
    fmap (\x -> s { _protocolVersion = x }) (k (_protocolVersion s))

normalizer :: Functor f => LensLike' f (Status m) (ReifiedNormalizer X)
normalizer k s = fmap (\x -> s { _normalizer = x }) (k (_normalizer s))

startingContext :: Functor f => LensLike' f (Status m) (Context (Expr Src X))
startingContext k s =
    fmap (\x -> s { _startingContext = x }) (k (_startingContext s))

resolver
    :: Functor f
    => LensLike' f (Status m) (Import -> StateT (Status m) m (Expr Src Import))
resolver k s = fmap (\x -> s { _resolver = x }) (k (_resolver s))

{-| This exception indicates that there was an internal error in Dhall's
    import-related logic
    the `expected` type then the `extract` function must succeed.  If not, then
    this exception is thrown

    This exception indicates that an invalid `Type` was provided to the `input`
    function
-}
data InternalError = InternalError deriving (Typeable)


instance Show InternalError where
    show InternalError = unlines
        [ _ERROR <> ": Compiler bug                                                        "
        , "                                                                                "
        , "Explanation: This error message means that there is a bug in the Dhall compiler."
        , "You didn't do anything wrong, but if you would like to see this problem fixed   "
        , "then you should report the bug at:                                              "
        , "                                                                                "
        , "https://github.com/dhall-lang/dhall-haskell/issues                              "
        , "                                                                                "
        , "Please include the following text in your bug report:                           "
        , "                                                                                "
        , "```                                                                             "
        , "Header extraction failed even though the header type-checked                    "
        , "```                                                                             "
        ]
      where
        _ERROR :: String
        _ERROR = "\ESC[1;31mError\ESC[0m"

instance Exception InternalError

-- | Wrapper around `HttpException`s with a prettier `Show` instance.
--
-- In order to keep the library API constant even when the @with-http@ Cabal
-- flag is disabled the pretty error message is pre-rendered and the real
-- 'HttpExcepion' is stored in a 'Dynamic'
data PrettyHttpException = PrettyHttpException String Dynamic
    deriving (Typeable)

instance Exception PrettyHttpException

instance Show PrettyHttpException where
  show (PrettyHttpException msg _) = msg
