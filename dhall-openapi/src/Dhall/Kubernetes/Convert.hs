{-# LANGUAGE NamedFieldPuns   #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE QuasiQuotes      #-}

module Dhall.Kubernetes.Convert
  ( toTypes
  , toDefault
  , mkImport
  , toDefinition
  , pathSplitter
  , groupBySimpleModelName
  ) where

import Control.Applicative (empty)
import Data.Aeson
import Data.Aeson.Types (Parser, parseMaybe)
import Data.Bifunctor (first, second)
import Data.Maybe (fromMaybe)
import Data.Scientific (Scientific)
import Data.Set (Set)
import Data.Text (Text)
import Dhall.Kubernetes.Types
import GHC.Generics (Generic, Rep)

import qualified Data.Char         as Char
import qualified Data.List         as List
import qualified Data.Map.Strict   as Data.Map
import qualified Data.Maybe        as Maybe
import qualified Data.Set          as Set
import qualified Data.Sort         as Sort
import qualified Data.Text         as Text
import qualified Data.Tuple        as Tuple
import qualified Dhall.Core        as Dhall
import qualified Dhall.Map
import qualified Dhall.Optics

modelsToText :: ModelHierarchy -> [Text]
modelsToText = List.map (\ (ModelName unModelName) -> unModelName)

-- | Get all the required fields for a model
--   See https://kubernetes.io/docs/concepts/overview/working-with-objects/kubernetes-objects/#required-fields
--   TLDR: because k8s API allows PUTS etc with partial data,
--   it's not clear from the data types OR the API which
--   fields are required for A POST...
requiredFields :: ModelHierarchy -> Maybe (Set FieldName) -> Set FieldName
requiredFields modelHierarchy required
  = Set.difference
      (List.foldr Set.union (fromMaybe Set.empty required) [alwaysRequired, toAdd])
      toRemove
  where
    alwaysRequired = Set.fromList $ FieldName <$> [ "apiVersion", "kind", "metadata"]
    toAdd = fromMaybe Set.empty $ Data.Map.lookup modelHierarchy requiredConstraints
    toRemove = fromMaybe Set.empty $ Data.Map.lookup modelHierarchy notRequiredConstraints

    -- | Some models require keys that are not in the required set,
    --   but are in the docs or just work
    requiredConstraints = Data.Map.fromList [ ]

    -- | Some models should not require some keys, and this is not
    --   in the Swagger spec but just in the docs
    notRequiredConstraints = Data.Map.fromList
      [ ( [ModelName "io.k8s.api.core.v1.ObjectFieldSelector"]
        , Set.fromList [ FieldName "apiVersion" ]
        )
      , ( [ModelName "io.k8s.apimachinery.pkg.apis.meta.v1.StatusDetails"]
        , Set.fromList [ FieldName "kind" ]
        )
      , ( [ModelName "io.k8s.api.core.v1.PersistentVolumeClaim"]
        , Set.fromList [ FieldName "apiVersion", FieldName "kind" ]
        )
      , ( [ModelName "io.k8s.api.batch.v1beta1.JobTemplateSpec"]
        , Set.fromList [ FieldName "metadata" ]
        )
      , ( [ModelName "io.k8s.api.batch.v2alpha1.JobTemplateSpec"]
        , Set.fromList [ FieldName "metadata" ]
        )
      , ( [ModelName "io.k8s.api.core.v1.PodTemplateSpec"]
        , Set.fromList [ FieldName "metadata" ]
        )
      ]


-- | Get a filename from a Swagger ref
pathFromRef :: Ref -> Text
pathFromRef (Ref r) = (Text.split (== '/') r) List.!! 2

-- | Build an import from path components (note: they need to be in reverse order)
--   and a filename
mkImport :: Data.Map.Map Prefix Dhall.Import -> [Text] -> Text -> Dhall.Import
mkImport prefixMap components file =
  case Data.Map.toList filteredPrefixMap of
    []    -> localImport
    xs    -> (snd . head $ Sort.sortOn (Text.length . fst) xs) <> localImport
  where
    localImport = Dhall.Import{..}
    importMode = Dhall.Code
    importHashed = Dhall.ImportHashed{..}
    hash = Nothing
    importType = Dhall.Local Dhall.Here Dhall.File{..}
    directory = Dhall.Directory{..}
    filteredPrefixMap = Data.Map.filterWithKey (\k _ -> Text.isPrefixOf k file) prefixMap

-- | Get the namespaced object name if the Import points to it
namespacedObjectFromImport :: Dhall.Import -> Maybe Text
namespacedObjectFromImport Dhall.Import
  { importHashed = Dhall.ImportHashed
    { importType = Dhall.Local Dhall.Here Dhall.File
      { file = f }
    }
  } = Just $ Text.replace ".dhall" "" f
namespacedObjectFromImport _ = Nothing

-- | Get a Dhall Text literal from a lone string
toTextLit :: Text -> Expr
toTextLit str = Dhall.TextLit (Dhall.Chunks [] str)

-- | Merge maps and error on conflicts
mergeNoConflicts :: (Ord k, Eq a, Show a, Show k) => (a -> a -> Bool) -> Data.Map.Map k a -> Data.Map.Map k a -> Data.Map.Map k a
mergeNoConflicts canMerge = Data.Map.unionWithKey
                   (\key left right ->
                     if   canMerge left right
                     then left 
                     else error ("Cannot merge differing values " ++ show left ++ " and " ++ show right ++ " for key " ++ show key))

{- | Extract the 'ModelName' to be used when splitting a definition.

    This is considered a guess as it does not work with all types. Currently it uses the first word from the description
    appended to the largest prefix before the last @.@ of the parent.
-}
guessModelNameForSplit :: ModelHierarchy -> Definition -> Maybe ModelName
guessModelNameForSplit models definition = ModelName <$> ((<>) <$> toPrepend <*> firstWordOfDesc)
  where
    toPrepend :: Maybe Text.Text
    toPrepend = (Tuple.fst . Text.breakOnEnd (Text.pack ".") <$> (Maybe.listToMaybe $ modelsToText models))

    firstWordOfDesc :: Maybe Text.Text
    firstWordOfDesc = (Text.words <$> (description definition) >>= Maybe.listToMaybe)

{- | Given the @pathsAndModels@ Map provides a function to be used with 'toTypes' to split types at mostly arbitrary points

   The @pathsAndModels@ argument takes the form of a path to an optional 'ModelName'. Paths are of the format noted by
   'modelsToPath'. If a 'ModelName' is provided as a value for the given path, it will be returned (to be then used as
   the 'ModelName' for the nested definition. If no 'ModelName' is provided, 'guessModelNameForSplit' will try to guess.
   If that fails, 'Nothing' will be returned such that no split will be done by 'toTypes'
   
   Currently not all split points in for nested definitions are supported (in fact only types with a properties
   attribute are currently supported).
-}
pathSplitter :: Data.Map.Map ModelHierarchy (Maybe ModelName) -> ModelHierarchy -> Definition -> Maybe ModelName
pathSplitter pathsAndModels modelHierarchy definition
  | (Maybe.isJust $ properties definition) && Maybe.isJust model = model
  | otherwise = Nothing
  where
    model = case Data.Map.lookup modelHierarchy pathsAndModels of
      Just (Just m) -> Just m
      Just (Nothing) -> guessModelNameForSplit modelHierarchy definition
      Nothing -> Nothing

{-| Converts all the Swagger definitions to Dhall Types

    Note: we cannot do 1-to-1 conversion and we need the whole Map because
    many types reference other types so we need to access them to decide things
    like "should this key be optional"
-}
toTypes :: Data.Map.Map Prefix Dhall.Import -> ([ModelName] -> Definition -> Maybe ModelName) -> Data.Map.Map ModelName Definition -> Data.Map.Map ModelName Expr
toTypes prefixMap typeSplitter definitions = toTypes' prefixMap typeSplitter definitions Data.Map.empty

toTypes' :: Data.Map.Map Prefix Dhall.Import -> ([ModelName] -> Definition -> Maybe ModelName) -> Data.Map.Map ModelName Definition -> Data.Map.Map ModelName Expr -> Data.Map.Map ModelName Expr
toTypes' prefixMap typeSplitter definitions toMerge
  | Data.Map.null definitions = toMerge
  | otherwise = mergeNoConflicts (==) (toTypes' prefixMap typeSplitter newDefs modelMap) toMerge
     where

        -- some CRDs are equal all except for the top description. This is safe as the only usage of description
        -- is 'guessModelNameForSplit' which has already been called for the top definition
        equalsIgnoringDescription :: Definition -> Definition -> Bool
        equalsIgnoringDescription a b = a { description = description b } == b

        convertAndAccumWithKey :: ModelHierarchy -> Data.Map.Map ModelName Definition -> ModelName -> Definition -> (Data.Map.Map ModelName Definition, Expr)
        convertAndAccumWithKey modelHierarchy accDefs k v = (mergeNoConflicts equalsIgnoringDescription accDefs leftOverDefs, expr)
          where
             (expr, leftOverDefs) = convertToType (modelHierarchy ++ [k]) v

        (newDefs, modelMap) = Data.Map.mapAccumWithKey (convertAndAccumWithKey []) Data.Map.empty definitions
       
        kvList = Dhall.App Dhall.List $ Dhall.Record $ Dhall.Map.fromList
          [ ("mapKey", Dhall.makeRecordField Dhall.Text), ("mapValue", Dhall.makeRecordField Dhall.Text) ]
        intOrStringType = Dhall.Union $ Dhall.Map.fromList $ fmap (second Just)
          [ ("Int", Dhall.Integer), ("String", Dhall.Text) ]

        -- | Convert a single Definition to a Dhall Type, yielding any definitions to be split
        --   Note: model hierarchy contains the modelName of of the current definition as the last entry
        convertToType :: ModelHierarchy -> Definition -> (Expr, Data.Map.Map ModelName Definition)
        convertToType modelHierarchy definition
          | Just splitModelName <- typeSplitter modelHierarchy definition =
            ( Dhall.Embed $ mkImport prefixMap [] ((unModelName splitModelName) <> ".dhall"), Data.Map.singleton splitModelName definition)
          -- If we point to a ref we just reference it via Import
          | Just r <- ref definition = ( Dhall.Embed $ mkImport prefixMap [] (pathFromRef r <> ".dhall"), Data.Map.empty)
          | Just props <- properties definition =
              let
                  shouldBeRequired :: ModelHierarchy -> FieldName -> Bool
                  shouldBeRequired hierarchy field = Set.member field requiredNames
                    where
                      requiredNames = requiredFields hierarchy (required definition)
                  
                  (newPropDefs, propModelMap) = Data.Map.mapAccumWithKey (convertAndAccumWithKey modelHierarchy) Data.Map.empty props

                  (required', optional') = Data.Map.partitionWithKey
                      (\k _ -> shouldBeRequired modelHierarchy (FieldName (unModelName k)))
                    -- TODO: labelize
                    $ propModelMap

                  allFields
                    = Data.Map.toList required'
                    <> fmap (second $ Dhall.App Dhall.Optional) (Data.Map.toList optional')

                  adaptRecordList = Dhall.Map.mapMaybe (Just . Dhall.makeRecordField)

              in (Dhall.Record $ adaptRecordList $ Dhall.Map.fromList $ fmap (first $ unModelName) allFields, newPropDefs)
            -- This is another way to declare an intOrString
          | Maybe.isJust $ intOrString definition = (intOrStringType, Data.Map.empty)
            -- Otherwise - if we have a 'type' - it's a basic type
          | Just basic <- typ definition = case basic of
              "object"  -> (kvList, Data.Map.empty)
              "array"   | Just item <- items definition ->
                let (e, tm) = convertToType (modelHierarchy) item
                in (Dhall.App Dhall.List e, tm)
              "string"  | format definition == Just "int-or-string" -> (intOrStringType, Data.Map.empty)
              "string"  -> (Dhall.Text, Data.Map.empty)
              "boolean" -> (Dhall.Bool, Data.Map.empty)
              "integer" -> case (minimum_ definition, exclusiveMinimum definition) of
                (Just min_, Just True) | min_ >= -1 -> (Dhall.Natural, Data.Map.empty)
                (Just min_, _)         | min_ >= 0 -> (Dhall.Natural, Data.Map.empty)
                _                      -> (Dhall.Integer, Data.Map.empty)
              "number"  -> (Dhall.Double, Data.Map.empty)
              other     -> error $ "Found missing Swagger type: " <> Text.unpack other
            -- There are empty schemas that only have a description, so we return empty record
          | otherwise = (Dhall.Record mempty, Data.Map.empty)

-- | Convert a Dhall Type to its default value
toDefault
  :: Data.Map.Map Prefix Dhall.Import  -- ^ Mapping of prefixes to import roots
  -> Data.Map.Map ModelName Definition -- ^ All the Swagger definitions
  -> ModelName                         -- ^ The name of the object we're converting
  -> Expr                              -- ^ The Dhall type of the object
  -> Maybe Expr
toDefault prefixMap definitions modelName = go
  where
    go = \case
      -- If we have an import, we also import in the default
      e@(Dhall.Embed _) -> Just e
      -- For a sum type, there is no obvious default value
      Dhall.Union _ -> Nothing
      -- Dynamic records (i.e. List { mapKey : Text, mapValue : Text }) also
      -- don't have default
      Dhall.App Dhall.List _ -> Nothing
      -- Simple types should not have a default
      Dhall.Text -> Nothing
      Dhall.Natural -> Nothing
      -- But most of the times we are dealing with a record.
      -- Here we transform the record type in a value, transforming the keys in
      -- this way:
      --
      --   * take the BaseData from definition and populate it
      --   * skip other required fields, except if they are records
      --   * set the optional fields to None and the lists to empty
      Dhall.Record kvsf ->
        let getBaseData :: Maybe Definition -> Dhall.Map.Map Text Expr
            getBaseData (Just Definition{ baseData = Just BaseData{..} }) =
                Dhall.Map.fromList
                    [ ("apiVersion", toTextLit apiVersion)
                    , ("kind"      , toTextLit kind      )
                    ]
            getBaseData _ = mempty

            baseData = getBaseData $ Data.Map.lookup modelName definitions

            -- | Given a Dhall type from a record field, figure out if and what
            --   default value it should have
            valueForField :: Expr -> Maybe Expr
            valueForField = \case
                Dhall.App Dhall.Optional _T -> do
                    let expression = Dhall.App Dhall.None _T

                    let adjustedExpression =
                            Dhall.Optics.transformOf
                              Dhall.subExpressions
                              adjustImport
                              expression

                    return adjustedExpression
                _ -> do
                    empty

            kvs = Dhall.Map.mapMaybe (Just . Dhall.recordFieldValue) kvsf

            adaptRecordMap = Dhall.Map.mapMaybe (Just . Dhall.makeRecordField)

            -- The main reason for adding this special case is so that the
            -- `apiVersion` and `kind` fields default to `Some …` instead of
            -- `None …`.
            combine l (Dhall.App Dhall.None _T) = Dhall.Some l
            combine _  r                        = r

        in  Just $ Dhall.RecordLit $ adaptRecordMap $ Dhall.Map.unionWith combine baseData (Dhall.Map.mapMaybe valueForField kvs)

      -- We error out here because wildcards are bad, and we should know if
      -- we get something unexpected
      e -> error $ show modelName <> "\n\n" <> show e

    -- | The imports that we get from the types are referring to the local folder,
    --   but if we want to refer them from the defaults we need to adjust the path
    adjustImport :: Expr -> Expr
    adjustImport (Dhall.Embed imp) | Just file <- namespacedObjectFromImport imp
      = Dhall.Embed $ mkImport prefixMap ["types", ".."] (file <> ".dhall")
    adjustImport other = other

-- | Given a list of fully namespaced models, it will group them by the
--   object name resolving duplicates with the given function
groupBySimpleModelName :: DuplicateHandler -> [ModelName] -> Data.Map.Map SimpleModelName ModelName
groupBySimpleModelName duplicateNameHandler models = Data.Map.mapMaybe selectObject $ groupBySimpleName models
  where
    groupBySimpleName :: [ModelName] -> Data.Map.Map SimpleModelName [ModelName]
    groupBySimpleName modelNames = Data.Map.unionsWith (<>)
      $ (\name -> Data.Map.singleton (toSimpleModelName name) [name])
      <$> modelNames

    toSimpleModelName :: ModelName -> SimpleModelName
    toSimpleModelName (ModelName name) =
      let elems = Text.split (== '.') name
      in elems List.!! (length elems - 1)

    -- | There will be more than one namespaced object for a single object name
    --   (because different API versions, and objects move around packages but k8s
    --   cannot break compatibility so we have all of them), so we have to select one
    --   (and we error out if it's not so after the filtering)
    selectObject :: ([ModelName]) -> Maybe ModelName
    selectObject (namespacedNames) = namespaced
      where
        filterFn (ModelName name) = not $ or
          -- The reason why we filter these two prefixes is that they are "internal"
          -- objects. I.e. they do not appear referenced in other objects, but are
          -- just in the Go source. E.g. see https://godoc.org/k8s.io/kubernetes/pkg/apis/core
          [ Text.isPrefixOf "io.k8s.kubernetes.pkg.api." name
          , Text.isPrefixOf "io.k8s.kubernetes.pkg.apis." name
          -- We keep a list of "old" objects that should not be preferred/picked
          ]

        namespaced = case filter filterFn namespacedNames of
          [name] -> Just name
          []     -> Nothing
          names  -> duplicateNameHandler (names)

stripPrefix :: (Generic a, GFromJSON Zero (Rep a)) => Int -> Value -> Parser a
stripPrefix n = genericParseJSON options
  where
    options = defaultOptions { fieldLabelModifier }

    removePrefix string = case drop n string of
                                  s : tring -> Char.toLower s : tring
                                  []        -> []
    extensionRename string = case string of
      "IntOrString" -> "x-kubernetes-int-or-string"
      a -> a

    fieldLabelModifier = removePrefix . extensionRename

data V1CustomResourceDefinition =
    V1CustomResourceDefinition
        { v1CustomResourceDefinitionSpec :: V1CustomResourceDefinitionSpec
        }
    deriving (Generic)


instance FromJSON V1CustomResourceDefinition where
    parseJSON = stripPrefix 26

data V1CustomResourceDefinitionSpec =
    V1CustomResourceDefinitionSpec
        { v1CustomResourceDefinitionSpecGroup :: Text
        , v1CustomResourceDefinitionSpecNames :: V1CustomResourceDefinitionNames
        , v1CustomResourceDefinitionSpecVersions :: Maybe [V1CustomResourceDefinitionVersion]
        } deriving (Generic)

instance FromJSON V1CustomResourceDefinitionSpec where
    parseJSON = stripPrefix 30

data V1CustomResourceDefinitionNames =
    V1CustomResourceDefinitionNames
        { v1CustomResourceDefinitionNamesKind :: Text
        } deriving (Generic)

instance FromJSON V1CustomResourceDefinitionNames where
    parseJSON = stripPrefix 31

data V1CustomResourceValidation =
    V1CustomResourceValidation
        { v1CustomResourceValidationOpenAPIV3Schema :: Maybe V1JSONSchemaProps
        } deriving (Generic)

instance FromJSON V1CustomResourceValidation where
    parseJSON = stripPrefix 26

data V1CustomResourceDefinitionVersion =
    V1CustomResourceDefinitionVersion
        { v1CustomResourceDefinitionVersionName :: Text
        , v1CustomResourceDefinitionVersionSchema :: Maybe V1CustomResourceValidation
        } deriving (Generic)

instance FromJSON V1CustomResourceDefinitionVersion where
    parseJSON = stripPrefix 33

data V1JSONSchemaProps =
    V1JSONSchemaProps
        { v1JSONSchemaPropsRef :: Maybe Text
        , v1JSONSchemaPropsDescription :: Maybe Text
        , v1JSONSchemaPropsFormat :: Maybe Text
        , v1JSONSchemaPropsMinimum :: Maybe Scientific
        , v1JSONSchemaPropsExclusiveMinimum :: Maybe Bool
        , v1JSONSchemaPropsItems :: Maybe Value
        , v1JSONSchemaPropsProperties :: Maybe (Data.Map.Map String V1JSONSchemaProps)
        , v1JSONSchemaPropsRequired :: Maybe [Text]
        , v1JSONSchemaPropsType :: Maybe Text
        , v1JSONSchemaPropsIntOrString :: Maybe Bool
        } deriving (Generic)

instance FromJSON V1JSONSchemaProps where
    parseJSON = stripPrefix 17

mkV1JSONSchemaProps :: V1JSONSchemaProps
mkV1JSONSchemaProps =
    V1JSONSchemaProps
        { v1JSONSchemaPropsRef = Nothing
        , v1JSONSchemaPropsDescription = Nothing
        , v1JSONSchemaPropsFormat = Nothing
        , v1JSONSchemaPropsMinimum = Nothing
        , v1JSONSchemaPropsExclusiveMinimum = Nothing
        , v1JSONSchemaPropsItems = Nothing
        , v1JSONSchemaPropsProperties = Nothing
        , v1JSONSchemaPropsRequired = Nothing
        , v1JSONSchemaPropsType = Nothing
        , v1JSONSchemaPropsIntOrString = Nothing
        }

orDie :: Maybe a -> e -> Either e a
Just r  `orDie` _ = Right r
Nothing `orDie` l = Left  l

toDefinition
    :: V1CustomResourceDefinition -> Either Text (ModelName, Definition)
toDefinition crd = fmap (\d -> (modelName, d)) definition
  where
    V1CustomResourceDefinition{..} = crd

    V1CustomResourceDefinitionSpec{..} = v1CustomResourceDefinitionSpec

    V1CustomResourceDefinitionNames{..} = v1CustomResourceDefinitionSpecNames

    modelName =
        ModelName (v1CustomResourceDefinitionSpecGroup <> "." <> v1CustomResourceDefinitionNamesKind)

    definition = do
      versions <- v1CustomResourceDefinitionSpecVersions
          `orDie` "The CustomResourceDefinitionSpec is missing the versions field"

      V1CustomResourceDefinitionVersion{..} <- case versions of
          [ version ] ->
              return version
          _ ->
              Left "This tool does not yet support more than one version for the versions field of the CustomResourceDefinitionSpec"

      V1CustomResourceValidation{..} <- v1CustomResourceDefinitionVersionSchema
          `orDie` "The CustomResourceDefinitionSpec is missing the schema field"

      openApiv3Schema <- v1CustomResourceValidationOpenAPIV3Schema
          `orDie` "The CustomResourceValidation is missing the openApiv3Schema field"

      let baseData = BaseData {
            kind = v1CustomResourceDefinitionNamesKind,

            apiVersion = v1CustomResourceDefinitionVersionName
          }

      let completeSchemaProperties =
            fmap
            (Data.Map.union
              (
                Data.Map.fromList [
                  ("apiVersion", (mkV1JSONSchemaProps {v1JSONSchemaPropsType = Just "string"}))
                , ("kind", (mkV1JSONSchemaProps {v1JSONSchemaPropsType = Just "string"} ))
                , ("metadata", mkV1JSONSchemaProps {v1JSONSchemaPropsType = Just "object", v1JSONSchemaPropsRef = Just "#/definitions/io.k8s.apimachinery.pkg.apis.meta.v1.ObjectMeta"} )
                ]
              ))
            (v1JSONSchemaPropsProperties openApiv3Schema)

      let completeSchema = openApiv3Schema { v1JSONSchemaPropsProperties = completeSchemaProperties}

      pure $ propsToDefinition completeSchema (Just baseData)

    propsToDefinition :: V1JSONSchemaProps -> Maybe BaseData -> Definition
    propsToDefinition V1JSONSchemaProps{..} basedata =
      Definition
        { typ              = v1JSONSchemaPropsType
        , ref              = Ref <$> v1JSONSchemaPropsRef
        , format           = v1JSONSchemaPropsFormat
        , minimum_         = v1JSONSchemaPropsMinimum
        , exclusiveMinimum = v1JSONSchemaPropsExclusiveMinimum
        , description      = v1JSONSchemaPropsDescription
        , items            = v1JSONSchemaPropsItems >>= parseMaybe parseJSON
        , properties       = fmap toProperties v1JSONSchemaPropsProperties
        , required         = fmap (Set.fromList . fmap FieldName) v1JSONSchemaPropsRequired
        , baseData         = basedata
        , intOrString      = v1JSONSchemaPropsIntOrString
        }

    toProperties :: Data.Map.Map String V1JSONSchemaProps -> Data.Map.Map ModelName Definition
    toProperties props =
      (Data.Map.fromList . fmap (\(k, p) -> ((ModelName . Text.pack) k, propsToDefinition p Nothing)) . Data.Map.toList) props
