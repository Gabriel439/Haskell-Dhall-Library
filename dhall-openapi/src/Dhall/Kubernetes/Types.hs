module Dhall.Kubernetes.Types where

import qualified Data.Text                 as Text
import qualified Data.Vector               as Vector
import qualified Dhall.Core                as Dhall
import qualified Dhall.Parser              as Dhall

import           Control.Applicative       (optional)
import           Control.Monad             (join)
import           Data.Aeson
import           Data.Map                  (Map)
import           Data.Scientific           (Scientific)
import           Data.Set                  (Set)
import           Data.Text                 (Text)
import           Data.Text.Prettyprint.Doc (Pretty)
import           GHC.Generics              (Generic)


type Expr = Dhall.Expr Dhall.Src Dhall.Import

type DuplicateHandler = [ModelName] -> Maybe ModelName
type AliasConverter = ModelName -> AliasedModelName

type Prefix = Text

type ModelHierarchy = [ModelName]

type AliasedModelName = Text

{-| Type for the Swagger specification.

There is such a type defined in the `swagger2` package, but Kubernetes' OpenAPI
file doesn't conform to that, so here we implement a small version of that
tailored to our needs.

-}
data Swagger = Swagger
  { definitions :: Map ModelName Definition
  } deriving (Generic, Show)

instance FromJSON Swagger


data Definition = Definition
  { typ              :: Maybe Text
  , ref              :: Maybe Ref
  , format           :: Maybe Text
  , minimum_         :: Maybe Scientific -- Avoid shadowing with Prelude.minimum
  , exclusiveMinimum :: Maybe Bool
  , description      :: Maybe Text
  , items            :: Maybe Definition
  , properties       :: Maybe (Map ModelName Definition)
  , required         :: Maybe (Set FieldName)
  , baseData         :: Maybe BaseData
  , intOrString      :: Maybe Bool
  } deriving (Generic, Show, Eq)

instance FromJSON Definition where
  parseJSON = withObject "definition" $ \o -> do
    typ              <- o .:? "type"
    ref              <- o .:? "$ref"
    format           <- o .:? "format"
    minimum_         <- o .:? "minimum"
    exclusiveMinimum <- o .:? "exclusiveMinimum"
    properties       <- o .:? "properties"
    required         <- o .:? "required"
    items            <- o .:? "items"
    description      <- o .:? "description"
    baseData         <- fmap join $ optional (o .:? "x-kubernetes-group-version-kind")
    intOrString      <- o .:? "x-kubernetes-int-or-string"
    pure Definition{..}


newtype Ref = Ref { unRef :: Text }
  deriving (Generic, Show, FromJSON, Eq)


newtype ModelName = ModelName { unModelName :: Text }
  deriving (Generic, Show, Ord, FromJSONKey, Eq, Pretty)

newtype FieldName = FieldName { unFieldName :: Text }
  deriving (Generic, Show, FromJSON, FromJSONKey, Ord, Eq, Pretty)


{-| This contains the static data that a Model might have

This applies only to kubernetes resources where ``kind`` and
``apiVersion`` are statically determined by the resource. See the
`Kubernetes OpenAPI Spec Readme`:
https://github.com/kubernetes/kubernetes/blob/master/api/openapi-spec/README.md#x-kubernetes-group-version-kind

For example for a v1 Deployment we have

{ kind = "Deployment"
, apiVersion = "apps/v1"
}

-}
data BaseData = BaseData
  { kind       :: Text
  , apiVersion :: Text
  } deriving (Generic, Show, Eq)

instance FromJSON BaseData where
  parseJSON = withArray "array of values" $ \arr -> withObject "baseData" (\o -> do
    group   <- o .:? "group" .!= ""
    kind    <- o .: "kind"
    version <- o .: "version"
    let apiVersion = (if Text.null group then "" else group <> "/") <> version
    pure BaseData{..})
    (head $ Vector.toList arr)
