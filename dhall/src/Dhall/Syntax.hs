{-# LANGUAGE DeriveAnyClass             #-}
{-# LANGUAGE DeriveDataTypeable         #-}
{-# LANGUAGE DeriveGeneric              #-}
{-# LANGUAGE DeriveLift                 #-}
{-# LANGUAGE DeriveTraversable          #-}
{-# LANGUAGE DerivingStrategies         #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase                 #-}
{-# LANGUAGE OverloadedLists            #-}
{-# LANGUAGE OverloadedStrings          #-}
{-# LANGUAGE RankNTypes                 #-}
{-# LANGUAGE RecordWildCards            #-}
{-# LANGUAGE StandaloneDeriving         #-}
{-# LANGUAGE UnicodeSyntax              #-}

{-# OPTIONS_GHC -Wno-orphans #-}

{-| This module contains the core syntax types and optics for them.

'reservedIdentifiers', 'denote' and friends are included because they are
involved in a dependency circle with "Dhall.Pretty.Internal".
-}

module Dhall.Syntax (
    -- * 'Expr'
      Const(..)
    , Var(..)
    , Binding(..)
    , makeBinding
    , CharacterSet(..)
    , Chunks(..)
    , DhallDouble(..)
    , PreferAnnotation(..)
    , Expr(..)
    , RecordField(..)
    , makeRecordField
    , FunctionBinding(..)
    , makeFunctionBinding
    , FieldSelection(..)
    , makeFieldSelection

    -- ** 'Let'-blocks
    , MultiLet(..)
    , multiLet
    , wrapInLets

    -- ** Optics
    , subExpressions
    , unsafeSubExpressions
    , chunkExprs
    , bindingExprs
    , recordFieldExprs
    , functionBindingExprs

    -- ** Handling 'Note's
    , denote
    , renote
    , shallowDenote

    -- * 'Import'
    , Directory(..)
    , File(..)
    , FilePrefix(..)
    , Import(..)
    , ImportHashed(..)
    , ImportMode(..)
    , ImportType(..)
    , URL(..)
    , Scheme(..)
    , pathCharacter

    -- * Reserved identifiers
    , reservedIdentifiers
    , reservedKeywords

    -- * `Data.Text.Text` manipulation
    , toDoubleQuoted
    , longestSharedWhitespacePrefix
    , linesLiteral
    , unlinesLiteral

    -- * Desugaring
    , desugarWith

    -- * Utilities
    , internalError
    -- `shift` should really be in `Dhall.Normalize`, but it's here to avoid a
    -- module cycle
    , shift
    ) where

import Control.DeepSeq            (NFData)
import Data.Bifunctor             (Bifunctor (..))
import Data.Bits                  (xor)
import Data.Data                  (Data)
import Data.Foldable
import Data.HashSet               (HashSet)
import Data.List.NonEmpty         (NonEmpty (..))
import Data.Sequence              (Seq)
import Data.String                (IsString (..))
import Data.Text                  (Text)
import Data.Text.Prettyprint.Doc  (Doc, Pretty)
import Data.Traversable           ()
import Data.Void                  (Void)
import Dhall.Map                  (Map)
import {-# SOURCE #-} Dhall.Pretty.Internal
import Dhall.Src                  (Src (..))
import GHC.Generics               (Generic)
import Instances.TH.Lift          ()
import Language.Haskell.TH.Syntax (Lift)
import Numeric.Natural            (Natural)
import Unsafe.Coerce              (unsafeCoerce)

import qualified Control.Monad
import qualified Data.Fixed                as Fixed
import qualified Data.HashSet
import qualified Data.List.NonEmpty        as NonEmpty
import qualified Data.Text
import qualified Data.Text.Prettyprint.Doc as Pretty
import qualified Data.Time                 as Time
import qualified Dhall.Crypto
import qualified Dhall.Optics              as Optics
import qualified Lens.Family               as Lens
import qualified Network.URI               as URI

deriving instance Lift Time.Day
deriving instance Lift Time.TimeOfDay
deriving instance Lift Time.TimeZone
deriving instance Lift (Fixed.Fixed a)

-- $setup
-- >>> import Dhall.Binary () -- For the orphan instance for `Serialise (Expr Void Import)`

{-| Constants for a pure type system

    The axioms are:

> ⊦ Type : Kind
> ⊦ Kind : Sort

    ... and the valid rule pairs are:

> ⊦ Type ↝ Type : Type  -- Functions from terms to terms (ordinary functions)
> ⊦ Kind ↝ Type : Type  -- Functions from types to terms (type-polymorphic functions)
> ⊦ Sort ↝ Type : Type  -- Functions from kinds to terms
> ⊦ Kind ↝ Kind : Kind  -- Functions from types to types (type-level functions)
> ⊦ Sort ↝ Kind : Sort  -- Functions from kinds to types (kind-polymorphic functions)
> ⊦ Sort ↝ Sort : Sort  -- Functions from kinds to kinds (kind-level functions)

    Note that Dhall does not support functions from terms to types and therefore
    Dhall is not a dependently typed language
-}
data Const = Type | Kind | Sort
    deriving (Show, Eq, Ord, Data, Bounded, Enum, Generic, Lift, NFData)

instance Pretty Const where
    pretty = Pretty.unAnnotate . prettyConst

{-| Label for a bound variable

    The `Data.Text.Text` field is the variable's name (i.e. \"@x@\").

    The `Int` field disambiguates variables with the same name if there are
    multiple bound variables of the same name in scope.  Zero refers to the
    nearest bound variable and the index increases by one for each bound
    variable of the same name going outward.  The following diagram may help:

>                               ┌──refers to──┐
>                               │             │
>                               v             │
> λ(x : Type) → λ(y : Type) → λ(x : Type) → x@0
>
> ┌─────────────────refers to─────────────────┐
> │                                           │
> v                                           │
> λ(x : Type) → λ(y : Type) → λ(x : Type) → x@1

    This `Int` behaves like a De Bruijn index in the special case where all
    variables have the same name.

    You can optionally omit the index if it is @0@:

>                               ┌─refers to─┐
>                               │           │
>                               v           │
> λ(x : Type) → λ(y : Type) → λ(x : Type) → x

    Zero indices are omitted when pretty-printing @Var@s and non-zero indices
    appear as a numeric suffix.
-}
data Var = V Text !Int
    deriving (Data, Generic, Eq, Ord, Show, Lift, NFData)

instance IsString Var where
    fromString str = V (fromString str) 0

instance Pretty Var where
    pretty = Pretty.unAnnotate . prettyVar

-- | Record the binding part of a @let@ expression.
--
-- For example,
--
-- > let {- A -} x {- B -} : {- C -} Bool = {- D -} True in x
--
-- … will be instantiated as follows:
--
-- * @bindingSrc0@ corresponds to the @A@ comment.
-- * @variable@ is @"x"@
-- * @bindingSrc1@ corresponds to the @B@ comment.
-- * @annotation@ is 'Just' a pair, corresponding to the @C@ comment and @Bool@.
-- * @bindingSrc2@ corresponds to the @D@ comment.
-- * @value@ corresponds to @True@.
data Binding s a = Binding
    { bindingSrc0 :: Maybe s
    , variable    :: Text
    , bindingSrc1 :: Maybe s
    , annotation  :: Maybe (Maybe s, Expr s a)
    , bindingSrc2 :: Maybe s
    , value       :: Expr s a
    } deriving (Data, Eq, Foldable, Functor, Generic, Lift, NFData, Ord, Show, Traversable)

instance Bifunctor Binding where
    first k (Binding src0 a src1 b src2 c) =
        Binding (fmap k src0) a (fmap k src1) (fmap adapt0 b) (fmap k src2) (first k c)
      where
        adapt0 (src3, d) = (fmap k src3, first k d)

    second = fmap

{-| Construct a 'Binding' with no source information and no type annotation.
-}
makeBinding :: Text -> Expr s a -> Binding s a
makeBinding name = Binding Nothing name Nothing Nothing Nothing

-- | This wrapper around 'Prelude.Double' exists for its 'Eq' instance which is
-- defined via the binary encoding of Dhall @Double@s.
newtype DhallDouble = DhallDouble { getDhallDouble :: Double }
    deriving stock (Show, Data, Lift, Generic)
    deriving anyclass NFData

-- | This instance satisfies all the customary 'Eq' laws except substitutivity.
--
-- In particular:
--
-- >>> nan = DhallDouble (0/0)
-- >>> nan == nan
-- True
--
-- This instance is also consistent with with the binary encoding of Dhall @Double@s:
--
-- >>> toBytes n = Dhall.Binary.encodeExpression (DoubleLit n :: Expr Void Import)
--
-- prop> \a b -> (a == b) == (toBytes a == toBytes b)
instance Eq DhallDouble where
    DhallDouble a == DhallDouble b
        | isNaN a && isNaN b                      = True
        | isNegativeZero a `xor` isNegativeZero b = False
        | otherwise                               = a == b

-- | This instance relies on the 'Eq' instance for 'DhallDouble' but cannot
-- satisfy the customary 'Ord' laws when @NaN@ is involved.
instance Ord DhallDouble where
    compare a@(DhallDouble a') b@(DhallDouble b') =
        if a == b
            then EQ
            else compare a' b'

-- | The body of an interpolated @Text@ literal
data Chunks s a = Chunks [(Text, Expr s a)] Text
    deriving (Functor, Foldable, Generic, Traversable, Show, Eq, Ord, Data, Lift, NFData)

instance Semigroup (Chunks s a) where
    Chunks xysL zL <> Chunks         []    zR =
        Chunks xysL (zL <> zR)
    Chunks xysL zL <> Chunks ((x, y):xysR) zR =
        Chunks (xysL ++ (zL <> x, y):xysR) zR

instance Monoid (Chunks s a) where
    mempty = Chunks [] mempty

instance IsString (Chunks s a) where
    fromString str = Chunks [] (fromString str)

-- | Used to record the origin of a @//@ operator (i.e. from source code or a
-- product of desugaring)
data PreferAnnotation s a
    = PreferFromSource
    | PreferFromWith (Expr s a)
      -- ^ Stores the original @with@ expression
    | PreferFromCompletion
    deriving (Data, Eq, Foldable, Functor, Generic, Lift, NFData, Ord, Show, Traversable)

instance Bifunctor PreferAnnotation where
    first _  PreferFromSource      = PreferFromSource
    first f (PreferFromWith e    ) = PreferFromWith (first f e)
    first _  PreferFromCompletion  = PreferFromCompletion

    second = fmap

-- | Record the field of a record-type and record-literal expression.
-- The reason why we use the same ADT for both of them is because they store
-- the same information.
--
-- For example,
--
-- > { {- A -} x {- B -} : {- C -} T }
--
-- ... or
--
-- > { {- A -} x {- B -} = {- C -} T }
--
-- will be instantiated as follows:
--
-- * @recordFieldSrc0@ corresponds to the @A@ comment.
-- * @recordFieldValue@ is @"T"@
-- * @recordFieldSrc1@ corresponds to the @B@ comment.
-- * @recordFieldSrc2@ corresponds to the @C@ comment.
--
-- Although the @A@ comment isn't annotating the @"T"@ Record Field,
-- this is the best place to keep these comments.
--
-- Note that @recordFieldSrc2@ is always 'Nothing' when the 'RecordField' is for
-- a punned entry, because there is no @=@ sign. For example,
--
-- > { {- A -} x {- B -} }
--
-- will be instantiated as follows:
--
-- * @recordFieldSrc0@ corresponds to the @A@ comment.
-- * @recordFieldValue@ corresponds to @(Var "x")@
-- * @recordFieldSrc1@ corresponds to the @B@ comment.
-- * @recordFieldSrc2@ will be 'Nothing'
--
-- The labels involved in a record using dot-syntax like in this example:
--
-- > { {- A -} a {- B -} . {- C -} b {- D -} . {- E -} c {- F -} = {- G -} e }
--
-- will be instantiated as follows:
--
-- * For both the @a@ and @b@ field, @recordfieldSrc2@ is 'Nothing'
-- * For the @a@ field:
--   * @recordFieldSrc0@ corresponds to the @A@ comment
--   * @recordFieldSrc1@ corresponds to the @B@ comment
-- * For the @b@ field:
--   * @recordFieldSrc0@ corresponds to the @C@ comment
--   * @recordFieldSrc1@ corresponds to the @D@ comment
-- * For the @c@ field:
--   * @recordFieldSrc0@ corresponds to the @E@ comment
--   * @recordFieldSrc1@ corresponds to the @F@ comment
--   * @recordFieldSrc2@ corresponds to the @G@ comment
--
-- That is, for every label except the last one the semantics of
-- @recordFieldSrc0@ and @recordFieldSrc1@ are the same from a regular record
-- label but @recordFieldSrc2@ is always 'Nothing'. For the last keyword, all
-- srcs are 'Just'
data RecordField s a = RecordField
    { recordFieldSrc0  :: Maybe s
    , recordFieldValue :: Expr s a
    , recordFieldSrc1  :: Maybe s
    , recordFieldSrc2  :: Maybe s
    } deriving (Data, Eq, Foldable, Functor, Generic, Lift, NFData, Ord, Show, Traversable)

-- | Construct a 'RecordField' with no src information
makeRecordField :: Expr s a -> RecordField s a
makeRecordField e = RecordField Nothing e Nothing Nothing


instance Bifunctor RecordField where
    first k (RecordField s0 value s1 s2) =
        RecordField (k <$> s0) (first k value) (k <$> s1) (k <$> s2)
    second = fmap

{-| Record the label of a function or a function-type expression

For example,

> λ({- A -} a {- B -} : {- C -} T) -> e

will be instantiated as follows:
* @functionBindingSrc0@ corresponds to the @A@ comment
* @functionBindingVariable@ is @a@
* @functionBindingSrc1@ corresponds to the @B@ comment
* @functionBindingSrc2@ corresponds to the @C@ comment
* @functionBindingAnnotation@ is @T@
-}
data FunctionBinding s a = FunctionBinding
    { functionBindingSrc0 :: Maybe s
    , functionBindingVariable :: Text
    , functionBindingSrc1 :: Maybe s
    , functionBindingSrc2 :: Maybe s
    , functionBindingAnnotation :: Expr s a
    } deriving (Data, Eq, Foldable, Functor, Generic, Lift, NFData, Ord, Show, Traversable)

-- | Smart constructor for 'FunctionBinding' with no src information
makeFunctionBinding :: Text -> Expr s a -> FunctionBinding s a
makeFunctionBinding l t = FunctionBinding Nothing l Nothing Nothing t

instance Bifunctor FunctionBinding where
    first k (FunctionBinding src0 label src1 src2 type_) =
        FunctionBinding (k <$> src0) label (k <$> src1) (k <$> src2) (first k type_)

    second = fmap

-- | Record the field on a selector-expression
--
-- For example,
--
-- > e . {- A -} x {- B -}
--
-- … will be instantiated as follows:
--
-- * @fieldSelectionSrc0@ corresponds to the @A@ comment
-- * @fieldSelectionLabel@ corresponds to @x@
-- * @fieldSelectionSrc1@ corresponds to the @B@ comment
--
-- Given our limitation that not all expressions recover their whitespaces, the
-- purpose of @fieldSelectionSrc1@ is to save the 'Text.Megaparsec.SourcePos'
-- where the @fieldSelectionLabel@ ends, but we /still/ use a 'Maybe Src'
-- (@s = 'Src'@) to be consistent with similar data types such as 'Binding', for
-- example.
data FieldSelection s = FieldSelection
    { fieldSelectionSrc0 :: Maybe s
    , fieldSelectionLabel :: !Text
    , fieldSelectionSrc1 :: Maybe s
    } deriving (Data, Eq, Foldable, Functor, Generic, Lift, NFData, Ord, Show, Traversable)

-- | Smart constructor for 'FieldSelection' with no src information
makeFieldSelection :: Text -> FieldSelection s
makeFieldSelection t = FieldSelection Nothing t Nothing

{-| Syntax tree for expressions

    The @s@ type parameter is used to track the presence or absence of `Src`
    spans:

    * If @s = `Src`@ then the code may contains `Src` spans (either in a `Note`
      constructor or inline within another constructor, like `Let`)
    * If @s = `Void`@ then the code has no `Src` spans

    The @a@ type parameter is used to track the presence or absence of imports

    * If @a = `Import`@ then the code may contain unresolved `Import`s
    * If @a = `Void`@ then the code has no `Import`s
-}
data Expr s a
    -- | > Const c                                  ~  c
    = Const Const
    -- | > Var (V x 0)                              ~  x
    --   > Var (V x n)                              ~  x@n
    | Var Var
    -- | > Lam _ (FunctionBinding _ "x" _ _ A) b    ~  λ(x : A) -> b
    | Lam (Maybe CharacterSet) (FunctionBinding s a) (Expr s a)
    -- | > Pi _ "_" A B                               ~        A  -> B
    --   > Pi _ x   A B                               ~  ∀(x : A) -> B
    | Pi  (Maybe CharacterSet) Text (Expr s a) (Expr s a)
    -- | > App f a                                  ~  f a
    | App (Expr s a) (Expr s a)
    -- | > Let (Binding _ x _  Nothing  _ r) e      ~  let x     = r in e
    --   > Let (Binding _ x _ (Just t ) _ r) e      ~  let x : t = r in e
    --
    -- The difference between
    --
    -- > let x = a    let y = b in e
    --
    -- and
    --
    -- > let x = a in let y = b in e
    --
    -- is only an additional 'Note' around @'Let' "y" …@ in the second
    -- example.
    --
    -- See 'MultiLet' for a representation of let-blocks that mirrors the
    -- source code more closely.
    | Let (Binding s a) (Expr s a)
    -- | > Annot x t                                ~  x : t
    | Annot (Expr s a) (Expr s a)
    -- | > Bool                                     ~  Bool
    | Bool
    -- | > BoolLit b                                ~  b
    | BoolLit Bool
    -- | > BoolAnd x y                              ~  x && y
    | BoolAnd (Expr s a) (Expr s a)
    -- | > BoolOr  x y                              ~  x || y
    | BoolOr  (Expr s a) (Expr s a)
    -- | > BoolEQ  x y                              ~  x == y
    | BoolEQ  (Expr s a) (Expr s a)
    -- | > BoolNE  x y                              ~  x != y
    | BoolNE  (Expr s a) (Expr s a)
    -- | > BoolIf x y z                             ~  if x then y else z
    | BoolIf (Expr s a) (Expr s a) (Expr s a)
    -- | > Natural                                  ~  Natural
    | Natural
    -- | > NaturalLit n                             ~  n
    | NaturalLit Natural
    -- | > NaturalFold                              ~  Natural/fold
    | NaturalFold
    -- | > NaturalBuild                             ~  Natural/build
    | NaturalBuild
    -- | > NaturalIsZero                            ~  Natural/isZero
    | NaturalIsZero
    -- | > NaturalEven                              ~  Natural/even
    | NaturalEven
    -- | > NaturalOdd                               ~  Natural/odd
    | NaturalOdd
    -- | > NaturalToInteger                         ~  Natural/toInteger
    | NaturalToInteger
    -- | > NaturalShow                              ~  Natural/show
    | NaturalShow
    -- | > NaturalSubtract                          ~  Natural/subtract
    | NaturalSubtract
    -- | > NaturalPlus x y                          ~  x + y
    | NaturalPlus (Expr s a) (Expr s a)
    -- | > NaturalTimes x y                         ~  x * y
    | NaturalTimes (Expr s a) (Expr s a)
    -- | > Integer                                  ~  Integer
    | Integer
    -- | > IntegerLit n                             ~  ±n
    | IntegerLit Integer
    -- | > IntegerClamp                             ~  Integer/clamp
    | IntegerClamp
    -- | > IntegerNegate                            ~  Integer/negate
    | IntegerNegate
    -- | > IntegerShow                              ~  Integer/show
    | IntegerShow
    -- | > IntegerToDouble                          ~  Integer/toDouble
    | IntegerToDouble
    -- | > Double                                   ~  Double
    | Double
    -- | > DoubleLit n                              ~  n
    | DoubleLit DhallDouble
    -- | > DoubleShow                               ~  Double/show
    | DoubleShow
    -- | > Text                                     ~  Text
    | Text
    -- | > TextLit (Chunks [(t1, e1), (t2, e2)] t3) ~  "t1${e1}t2${e2}t3"
    | TextLit (Chunks s a)
    -- | > TextAppend x y                           ~  x ++ y
    | TextAppend (Expr s a) (Expr s a)
    -- | > TextReplace                              ~ Text/replace
    | TextReplace
    -- | > TextShow                                 ~  Text/show
    | TextShow
    -- | > Date                                     ~  Date
    | Date
    -- | > DateLiteral (fromGregorian _YYYY _MM _DD) ~ YYYY-MM-DD
    | DateLiteral Time.Day
    -- | > Time                                     ~  Time
    | Time
    -- | > TimeLiteral (TimeOfDay hh mm ss) _       ~  hh:mm:ss
    | TimeLiteral
        Time.TimeOfDay
        Word
        -- ^ Precision
    -- | > TimeZone                                 ~  TimeZone
    | TimeZone
    -- | > TimeZoneLiteral (TimeZone ( 60 * _HH + _MM) _ _) ~ +HH:MM
    -- | > TimeZoneLiteral (TimeZone (-60 * _HH + _MM) _ _) ~ -HH:MM
    | TimeZoneLiteral Time.TimeZone
    -- | > List                                     ~  List
    | List
    -- | > ListLit (Just t ) []                     ~  [] : t
    --   > ListLit  Nothing  [x, y, z]              ~  [x, y, z]
    --
    --   Invariant: A non-empty list literal is always represented as
    --   @ListLit Nothing xs@.
    --
    --   When an annotated, non-empty list literal is parsed, it is represented
    --   as
    --
    --   > Annot (ListLit Nothing [x, y, z]) t      ~ [x, y, z] : t

    -- Eventually we should have separate constructors for empty and non-empty
    -- list literals. For now it's easier to check the invariant in @infer@.
    -- See https://github.com/dhall-lang/dhall-haskell/issues/1359#issuecomment-537087234.
    | ListLit (Maybe (Expr s a)) (Seq (Expr s a))
    -- | > ListAppend x y                           ~  x # y
    | ListAppend (Expr s a) (Expr s a)
    -- | > ListBuild                                ~  List/build
    | ListBuild
    -- | > ListFold                                 ~  List/fold
    | ListFold
    -- | > ListLength                               ~  List/length
    | ListLength
    -- | > ListHead                                 ~  List/head
    | ListHead
    -- | > ListLast                                 ~  List/last
    | ListLast
    -- | > ListIndexed                              ~  List/indexed
    | ListIndexed
    -- | > ListReverse                              ~  List/reverse
    | ListReverse
    -- | > Optional                                 ~  Optional
    | Optional
    -- | > Some e                                   ~  Some e
    | Some (Expr s a)
    -- | > None                                     ~  None
    | None
    -- | > Record [ (k1, RecordField _ t1)          ~  { k1 : t1, k2 : t1 }
    --   >        , (k2, RecordField _ t2)
    --   >        ]
    | Record    (Map Text (RecordField s a))
    -- | > RecordLit [ (k1, RecordField _ v1)       ~  { k1 = v1, k2 = v2 }
    --   >           , (k2, RecordField _ v2)
    --   >           ]
    | RecordLit (Map Text (RecordField s a))
    -- | > Union        [(k1, Just t1), (k2, Nothing)] ~  < k1 : t1 | k2 >
    | Union     (Map Text (Maybe (Expr s a)))
    -- | > Combine _ Nothing x y                    ~  x ∧ y
    --
    -- The first field is a `Just` when the `Combine` operator is introduced
    -- as a result of desugaring duplicate record fields:
    --
    --   > RecordLit [ ( k                          ~ { k = x, k = y }
    --   >           , RecordField
    --   >              _
    --   >              (Combine (Just k) x y)
    --   >            )]
    | Combine (Maybe CharacterSet) (Maybe Text) (Expr s a) (Expr s a)
    -- | > CombineTypes _ x y                       ~  x ⩓ y
    | CombineTypes (Maybe CharacterSet) (Expr s a) (Expr s a)
    -- | > Prefer _ False x y                       ~  x ⫽ y
    --
    -- The first field is a `True` when the `Prefer` operator is introduced as a
    -- result of desugaring a @with@ expression
    | Prefer (Maybe CharacterSet) (PreferAnnotation s a) (Expr s a) (Expr s a)
    -- | > RecordCompletion x y                     ~  x::y
    | RecordCompletion (Expr s a) (Expr s a)
    -- | > Merge x y (Just t )                      ~  merge x y : t
    --   > Merge x y  Nothing                       ~  merge x y
    | Merge (Expr s a) (Expr s a) (Maybe (Expr s a))
    -- | > ToMap x (Just t)                         ~  toMap x : t
    --   > ToMap x  Nothing                         ~  toMap x
    | ToMap (Expr s a) (Maybe (Expr s a))
    -- | > Field e (FieldSelection _ x _)              ~  e.x
    | Field (Expr s a) (FieldSelection s)
    -- | > Project e (Left xs)                      ~  e.{ xs }
    --   > Project e (Right t)                      ~  e.(t)
    | Project (Expr s a) (Either [Text] (Expr s a))
    -- | > Assert e                                 ~  assert : e
    | Assert (Expr s a)
    -- | > Equivalent _ x y                           ~  x ≡ y
    | Equivalent (Maybe CharacterSet) (Expr s a) (Expr s a)
    -- | > With x y e                               ~  x with y = e
    | With (Expr s a) (NonEmpty Text) (Expr s a)
    -- | > Note s x                                 ~  e
    | Note s (Expr s a)
    -- | > ImportAlt                                ~  e1 ? e2
    | ImportAlt (Expr s a) (Expr s a)
    -- | > Embed import                             ~  import
    | Embed a
    deriving (Foldable, Generic, Traversable, Show, Data, Lift, NFData)
-- NB: If you add a constructor to Expr, please also update the Arbitrary
-- instance in Dhall.Test.QuickCheck.

-- | This instance encodes what the Dhall standard calls an \"exact match\"
-- between two expressions.
--
-- Note that
--
-- >>> nan = DhallDouble (0/0)
-- >>> DoubleLit nan == DoubleLit nan
-- True
deriving instance (Eq s, Eq a) => Eq (Expr s a)

-- | Note that this 'Ord' instance inherits `DhallDouble`'s defects.
deriving instance (Ord s, Ord a) => Ord (Expr s a)

-- This instance is hand-written due to the fact that deriving
-- it does not give us an INLINABLE pragma. We annotate this fmap
-- implementation with this pragma below to allow GHC to, possibly,
-- inline the implementation for performance improvements.
instance Functor (Expr s) where
  fmap f (Embed a) = Embed (f a)
  fmap f (Let b e2) = Let (fmap f b) (fmap f e2)
  fmap f (Note s e1) = Note s (fmap f e1)
  fmap f (Record a) = Record $ fmap f <$> a
  fmap f (RecordLit a) = RecordLit $ fmap f <$> a
  fmap f (Lam cs fb e) = Lam cs (f <$> fb) (f <$> e)
  fmap f (Field a b) = Field (f <$> a) b
  fmap f expression = Lens.over unsafeSubExpressions (fmap f) expression
  {-# INLINABLE fmap #-}

instance Applicative (Expr s) where
    pure = Embed

    (<*>) = Control.Monad.ap

instance Monad (Expr s) where
    return = pure

    expression >>= k = case expression of
        Embed a     -> k a
        Let a b     -> Let (adaptBinding a) (b >>= k)
        Note a b    -> Note a (b >>= k)
        Record a    -> Record $ bindRecordKeyValues <$> a
        RecordLit a -> RecordLit $ bindRecordKeyValues <$> a
        Lam cs a b  -> Lam cs (adaptFunctionBinding a) (b >>= k)
        Field a b   -> Field (a >>= k) b
        _ -> Lens.over unsafeSubExpressions (>>= k) expression
      where
        bindRecordKeyValues (RecordField s0 e s1 s2) =
            RecordField s0 (e >>= k) s1 s2

        adaptBinding (Binding src0 c src1 d src2 e) =
            Binding src0 c src1 (fmap adaptBindingAnnotation d) src2 (e >>= k)

        adaptFunctionBinding (FunctionBinding src0 label src1 src2 type_) =
            FunctionBinding src0 label src1 src2 (type_ >>= k)

        adaptBindingAnnotation (src3, f) = (src3, f >>= k)

instance Bifunctor Expr where
    first k (Note a b   ) = Note (k a) (first k b)
    first _ (Embed a    ) = Embed a
    first k (Let a b    ) = Let (first k a) (first k b)
    first k (Record a   ) = Record $ first k <$> a
    first k (RecordLit a) = RecordLit $ first k <$> a
    first k (Lam cs a b ) = Lam cs (first k a) (first k b)
    first k (Field a b  ) = Field (first k a) (k <$> b)
    first k  expression  = Lens.over unsafeSubExpressions (first k) expression

    second = fmap

instance IsString (Expr s a) where
    fromString str = Var (fromString str)

-- | Generates a syntactically valid Dhall program
instance Pretty a => Pretty (Expr s a) where
    pretty = Pretty.unAnnotate . prettyExpr

{-
Instead of converting explicitly between 'Expr's and 'MultiLet', it might
be nicer to use a pattern synonym:

> pattern MultiLet' :: NonEmpty (Binding s a) -> Expr s a -> Expr s a
> pattern MultiLet' as b <- (multiLetFromExpr -> Just (MultiLet as b)) where
>   MultiLet' as b = wrapInLets as b
>
> multiLetFromExpr :: Expr s a -> Maybe (MultiLet s a)
> multiLetFromExpr = \case
>     Let x mA a b -> Just (multiLet x mA a b)
>     _ -> Nothing

This works in principle, but GHC as of v8.8.1 doesn't handle it well:
https://gitlab.haskell.org/ghc/ghc/issues/17096

This should be fixed by GHC-8.10, so it might be worth revisiting then.
-}

{-| Generate a 'MultiLet' from the contents of a 'Let'.

    In the resulting @'MultiLet' bs e@, @e@ is guaranteed not to be a 'Let',
    but it might be a @('Note' … ('Let' …))@.

    Given parser output, 'multiLet' consolidates @let@s that formed a
    let-block in the original source.
-}
multiLet :: Binding s a -> Expr s a -> MultiLet s a
multiLet b0 = \case
    Let b1 e1 ->
        let MultiLet bs e = multiLet b1 e1
        in  MultiLet (NonEmpty.cons b0 bs) e
    e -> MultiLet (b0 :| []) e

{-| Wrap let-'Binding's around an 'Expr'.

'wrapInLets' can be understood as an inverse for 'multiLet':

> let MultiLet bs e1 = multiLet b e0
>
> wrapInLets bs e1 == Let b e0
-}
wrapInLets :: Foldable f => f (Binding s a) -> Expr s a -> Expr s a
wrapInLets bs e = foldr Let e bs

{-| This type represents 1 or more nested `Let` bindings that have been
    coalesced together for ease of manipulation
-}
data MultiLet s a = MultiLet (NonEmpty (Binding s a)) (Expr s a)

-- | A traversal over the immediate sub-expressions of an expression.
subExpressions
    :: Applicative f => (Expr s a -> f (Expr s a)) -> Expr s a -> f (Expr s a)
subExpressions _ (Embed a) = pure (Embed a)
subExpressions f (Note a b) = Note a <$> f b
subExpressions f (Let a b) = Let <$> bindingExprs f a <*> f b
subExpressions f (Record a) = Record <$> traverse (recordFieldExprs f) a
subExpressions f (RecordLit a) = RecordLit <$> traverse (recordFieldExprs f) a
subExpressions f (Lam cs fb e) = Lam cs <$> functionBindingExprs f fb <*> f e
subExpressions f (Field a b) = Field <$> f a <*> pure b
subExpressions f expression = unsafeSubExpressions f expression
{-# INLINABLE subExpressions #-}

{-| An internal utility used to implement transformations that require changing
    one of the type variables of the `Expr` type

    This utility only works because the implementation is partial, not
    handling the `Let`, `Note`, or `Embed` cases, which need to be handled by
    the caller.
-}
unsafeSubExpressions
    :: Applicative f => (Expr s a -> f (Expr t b)) -> Expr s a -> f (Expr t b)
unsafeSubExpressions _ (Const c) = pure (Const c)
unsafeSubExpressions _ (Var v) = pure (Var v)
unsafeSubExpressions f (Pi cs a b c) = Pi cs a <$> f b <*> f c
unsafeSubExpressions f (App a b) = App <$> f a <*> f b
unsafeSubExpressions f (Annot a b) = Annot <$> f a <*> f b
unsafeSubExpressions _ Bool = pure Bool
unsafeSubExpressions _ (BoolLit b) = pure (BoolLit b)
unsafeSubExpressions f (BoolAnd a b) = BoolAnd <$> f a <*> f b
unsafeSubExpressions f (BoolOr a b) = BoolOr <$> f a <*> f b
unsafeSubExpressions f (BoolEQ a b) = BoolEQ <$> f a <*> f b
unsafeSubExpressions f (BoolNE a b) = BoolNE <$> f a <*> f b
unsafeSubExpressions f (BoolIf a b c) = BoolIf <$> f a <*> f b <*> f c
unsafeSubExpressions _ Natural = pure Natural
unsafeSubExpressions _ (NaturalLit n) = pure (NaturalLit n)
unsafeSubExpressions _ NaturalFold = pure NaturalFold
unsafeSubExpressions _ NaturalBuild = pure NaturalBuild
unsafeSubExpressions _ NaturalIsZero = pure NaturalIsZero
unsafeSubExpressions _ NaturalEven = pure NaturalEven
unsafeSubExpressions _ NaturalOdd = pure NaturalOdd
unsafeSubExpressions _ NaturalToInteger = pure NaturalToInteger
unsafeSubExpressions _ NaturalShow = pure NaturalShow
unsafeSubExpressions _ NaturalSubtract = pure NaturalSubtract
unsafeSubExpressions f (NaturalPlus a b) = NaturalPlus <$> f a <*> f b
unsafeSubExpressions f (NaturalTimes a b) = NaturalTimes <$> f a <*> f b
unsafeSubExpressions _ Integer = pure Integer
unsafeSubExpressions _ (IntegerLit n) = pure (IntegerLit n)
unsafeSubExpressions _ IntegerClamp = pure IntegerClamp
unsafeSubExpressions _ IntegerNegate = pure IntegerNegate
unsafeSubExpressions _ IntegerShow = pure IntegerShow
unsafeSubExpressions _ IntegerToDouble = pure IntegerToDouble
unsafeSubExpressions _ Double = pure Double
unsafeSubExpressions _ (DoubleLit n) = pure (DoubleLit n)
unsafeSubExpressions _ DoubleShow = pure DoubleShow
unsafeSubExpressions _ Text = pure Text
unsafeSubExpressions f (TextLit chunks) =
    TextLit <$> chunkExprs f chunks
unsafeSubExpressions f (TextAppend a b) = TextAppend <$> f a <*> f b
unsafeSubExpressions _ TextReplace = pure TextReplace
unsafeSubExpressions _ TextShow = pure TextShow
unsafeSubExpressions _ Date = pure Date
unsafeSubExpressions _ (DateLiteral a) = pure (DateLiteral a)
unsafeSubExpressions _ Time = pure Time
unsafeSubExpressions _ (TimeLiteral a b) = pure (TimeLiteral a b)
unsafeSubExpressions _ TimeZone = pure TimeZone
unsafeSubExpressions _ (TimeZoneLiteral a) = pure (TimeZoneLiteral a)
unsafeSubExpressions _ List = pure List
unsafeSubExpressions f (ListLit a b) = ListLit <$> traverse f a <*> traverse f b
unsafeSubExpressions f (ListAppend a b) = ListAppend <$> f a <*> f b
unsafeSubExpressions _ ListBuild = pure ListBuild
unsafeSubExpressions _ ListFold = pure ListFold
unsafeSubExpressions _ ListLength = pure ListLength
unsafeSubExpressions _ ListHead = pure ListHead
unsafeSubExpressions _ ListLast = pure ListLast
unsafeSubExpressions _ ListIndexed = pure ListIndexed
unsafeSubExpressions _ ListReverse = pure ListReverse
unsafeSubExpressions _ Optional = pure Optional
unsafeSubExpressions f (Some a) = Some <$> f a
unsafeSubExpressions _ None = pure None
unsafeSubExpressions f (Union a) = Union <$> traverse (traverse f) a
unsafeSubExpressions f (Combine cs a b c) = Combine cs a <$> f b <*> f c
unsafeSubExpressions f (CombineTypes cs a b) = CombineTypes cs <$> f a <*> f b
unsafeSubExpressions f (Prefer cs a b c) = Prefer cs <$> a' <*> f b <*> f c
  where
    a' = case a of
        PreferFromSource     -> pure PreferFromSource
        PreferFromWith d     -> PreferFromWith <$> f d
        PreferFromCompletion -> pure PreferFromCompletion
unsafeSubExpressions f (RecordCompletion a b) = RecordCompletion <$> f a <*> f b
unsafeSubExpressions f (Merge a b t) = Merge <$> f a <*> f b <*> traverse f t
unsafeSubExpressions f (ToMap a t) = ToMap <$> f a <*> traverse f t
unsafeSubExpressions f (Project a b) = Project <$> f a <*> traverse f b
unsafeSubExpressions f (Assert a) = Assert <$> f a
unsafeSubExpressions f (Equivalent cs a b) = Equivalent cs <$> f a <*> f b
unsafeSubExpressions f (With a b c) = With <$> f a <*> pure b <*> f c
unsafeSubExpressions f (ImportAlt l r) = ImportAlt <$> f l <*> f r
unsafeSubExpressions _ (Let {}) = unhandledConstructor "Let"
unsafeSubExpressions _ (Note {}) = unhandledConstructor "Note"
unsafeSubExpressions _ (Embed {}) = unhandledConstructor "Embed"
unsafeSubExpressions _ (Record {}) = unhandledConstructor "Record"
unsafeSubExpressions _ (RecordLit {}) = unhandledConstructor "RecordLit"
unsafeSubExpressions _ (Lam {}) = unhandledConstructor "Lam"
unsafeSubExpressions _ (Field {}) = unhandledConstructor "Field"
{-# INLINABLE unsafeSubExpressions #-}

unhandledConstructor :: Text -> a
unhandledConstructor constructor =
    internalError
        (   "Dhall.Syntax.unsafeSubExpressions: Unhandled "
        <>  constructor
        <>  " construtor"
        )

{-| Traverse over the immediate 'Expr' children in a 'Binding'.
-}
bindingExprs
  :: (Applicative f)
  => (Expr s a -> f (Expr s b))
  -> Binding s a -> f (Binding s b)
bindingExprs f (Binding s0 n s1 t s2 v) =
  Binding
    <$> pure s0
    <*> pure n
    <*> pure s1
    <*> traverse (traverse f) t
    <*> pure s2
    <*> f v
{-# INLINABLE bindingExprs #-}

{-| Traverse over the immediate 'Expr' children in a 'RecordField'.
-}
recordFieldExprs
    :: Applicative f
    => (Expr s a -> f (Expr s b))
    -> RecordField s a -> f (RecordField s b)
recordFieldExprs f (RecordField s0 e s1 s2) =
    RecordField
        <$> pure s0
        <*> f e
        <*> pure s1
        <*> pure s2
{-# INLINABLE recordFieldExprs #-}

{-| Traverse over the immediate 'Expr' children in a 'FunctionBinding'.
-}
functionBindingExprs
    :: Applicative f
    => (Expr s a -> f (Expr s b))
    -> FunctionBinding s a -> f (FunctionBinding s b)
functionBindingExprs f (FunctionBinding s0 label s1 s2 type_) =
    FunctionBinding
        <$> pure s0
        <*> pure label
        <*> pure s1
        <*> pure s2
        <*> f type_
{-# INLINABLE functionBindingExprs #-}

-- | A traversal over the immediate sub-expressions in 'Chunks'.
chunkExprs
  :: Applicative f
  => (Expr s a -> f (Expr t b))
  -> Chunks s a -> f (Chunks t b)
chunkExprs f (Chunks chunks final) =
  flip Chunks final <$> traverse (traverse f) chunks
{-# INLINABLE chunkExprs #-}

{-| Internal representation of a directory that stores the path components in
    reverse order

    In other words, the directory @\/foo\/bar\/baz@ is encoded as
    @Directory { components = [ "baz", "bar", "foo" ] }@
-}
newtype Directory = Directory { components :: [Text] }
    deriving stock (Eq, Generic, Ord, Show)
    deriving anyclass NFData

instance Semigroup Directory where
    Directory components₀ <> Directory components₁ =
        Directory (components₁ <> components₀)

instance Pretty Directory where
    pretty (Directory {..}) = foldMap prettyPathComponent (reverse components)

prettyPathComponent :: Text -> Doc ann
prettyPathComponent text
    | Data.Text.all pathCharacter text =
        "/" <> Pretty.pretty text
    | otherwise =
        "/\"" <> Pretty.pretty text <> "\""

{-| A `File` is a `directory` followed by one additional path component
    representing the `file` name
-}
data File = File
    { directory :: Directory
    , file      :: Text
    } deriving (Eq, Generic, Ord, Show, NFData)

instance Pretty File where
    pretty (File {..}) =
            Pretty.pretty directory
        <>  prettyPathComponent file

instance Semigroup File where
    File directory₀ _ <> File directory₁ file =
        File (directory₀ <> directory₁) file

-- | The beginning of a file path which anchors subsequent path components
data FilePrefix
    = Absolute
    -- ^ Absolute path
    | Here
    -- ^ Path relative to @.@
    | Parent
    -- ^ Path relative to @..@
    | Home
    -- ^ Path relative to @~@
    deriving (Eq, Generic, Ord, Show, NFData)

instance Pretty FilePrefix where
    pretty Absolute = ""
    pretty Here     = "."
    pretty Parent   = ".."
    pretty Home     = "~"

-- | The URI scheme
data Scheme = HTTP | HTTPS deriving (Eq, Generic, Ord, Show, NFData)

-- | This type stores all of the components of a remote import
data URL = URL
    { scheme    :: Scheme
    , authority :: Text
    , path      :: File
    , query     :: Maybe Text
    , headers   :: Maybe (Expr Src Import)
    } deriving (Eq, Generic, Ord, Show, NFData)

instance Pretty URL where
    pretty (URL {..}) =
            schemeDoc
        <>  "://"
        <>  Pretty.pretty authority
        <>  pathDoc
        <>  queryDoc
        <>  foldMap prettyHeaders headers
      where
        prettyHeaders h =
          " using " <> Pretty.unAnnotate (prettyImportExpression h)

        File {..} = path

        Directory {..} = directory

        pathDoc =
                foldMap prettyURIComponent (reverse components)
            <>  prettyURIComponent file

        schemeDoc = case scheme of
            HTTP  -> "http"
            HTTPS -> "https"

        queryDoc = case query of
            Nothing -> ""
            Just q  -> "?" <> Pretty.pretty q

prettyURIComponent :: Text -> Doc ann
prettyURIComponent text =
        Pretty.pretty $ URI.normalizeCase $ URI.normalizeEscape $ "/" <> Data.Text.unpack text

-- | The type of import (i.e. local vs. remote vs. environment)
data ImportType
    = Local FilePrefix File
    -- ^ Local path
    | Remote URL
    -- ^ URL of remote resource and optional headers stored in an import
    | Env  Text
    -- ^ Environment variable
    | Missing
    deriving (Eq, Generic, Ord, Show, NFData)

parent :: File
parent = File { directory = Directory { components = [ ".." ] }, file = "" }

instance Semigroup ImportType where
    Local prefix file₀ <> Local Here file₁ = Local prefix (file₀ <> file₁)

    Remote (URL { path = path₀, ..}) <> Local Here path₁ =
        Remote (URL { path = path₀ <> path₁, ..})

    Local prefix file₀ <> Local Parent file₁ =
        Local prefix (file₀ <> parent <> file₁)

    Remote (URL { path = path₀, .. }) <> Local Parent path₁ =
        Remote (URL { path = path₀ <> parent <> path₁, .. })

    import₀ <> Remote (URL { headers = headers₀, .. }) =
        Remote (URL { headers = headers₁, .. })
      where
        importHashed₀ = Import (ImportHashed Nothing import₀) Code

        headers₁ = fmap (fmap (importHashed₀ <>)) headers₀

    _ <> import₁ =
        import₁

instance Pretty ImportType where
    pretty (Local prefix file) =
        Pretty.pretty prefix <> Pretty.pretty file

    pretty (Remote url) = Pretty.pretty url

    pretty (Env env) = "env:" <> prettyEnvironmentVariable env

    pretty Missing = "missing"

-- | How to interpret the import's contents (i.e. as Dhall code or raw text)
data ImportMode = Code | RawText | Location
  deriving (Eq, Generic, Ord, Show, NFData)

-- | A `ImportType` extended with an optional hash for semantic integrity checks
data ImportHashed = ImportHashed
    { hash       :: Maybe Dhall.Crypto.SHA256Digest
    , importType :: ImportType
    } deriving (Eq, Generic, Ord, Show, NFData)

instance Semigroup ImportHashed where
    ImportHashed _ importType₀ <> ImportHashed hash importType₁ =
        ImportHashed hash (importType₀ <> importType₁)

instance Pretty ImportHashed where
    pretty (ImportHashed  Nothing p) =
      Pretty.pretty p
    pretty (ImportHashed (Just h) p) =
      Pretty.group (Pretty.flatAlt long short)
      where
        long =
            Pretty.align
                (   Pretty.pretty p <> Pretty.hardline
                <>  "  sha256:" <> Pretty.pretty (show h)
                )

        short = Pretty.pretty p <> " sha256:" <> Pretty.pretty (show h)

-- | Reference to an external resource
data Import = Import
    { importHashed :: ImportHashed
    , importMode   :: ImportMode
    } deriving (Eq, Generic, Ord, Show, NFData)

instance Semigroup Import where
    Import importHashed₀ _ <> Import importHashed₁ code =
        Import (importHashed₀ <> importHashed₁) code

instance Pretty Import where
    pretty (Import {..}) = Pretty.pretty importHashed <> Pretty.pretty suffix
      where
        suffix :: Text
        suffix = case importMode of
            RawText  -> " as Text"
            Location -> " as Location"
            Code     -> ""

{-| Returns `True` if the given `Char` is valid within an unquoted path
    component

    This is exported for reuse within the @"Dhall.Parser.Token"@ module
-}
pathCharacter :: Char -> Bool
pathCharacter c =
         '\x21' == c
    ||  ('\x24' <= c && c <= '\x27')
    ||  ('\x2A' <= c && c <= '\x2B')
    ||  ('\x2D' <= c && c <= '\x2E')
    ||  ('\x30' <= c && c <= '\x3B')
    ||  c == '\x3D'
    ||  ('\x40' <= c && c <= '\x5A')
    ||  ('\x5E' <= c && c <= '\x7A')
    ||  c == '\x7C'
    ||  c == '\x7E'

-- | Remove all `Note` constructors from an `Expr` (i.e. de-`Note`)
--
-- This also remove CharacterSet annotations.
denote :: Expr s a -> Expr t a
denote = \case
    Note _ b -> denote b
    Let a b -> Let (denoteBinding a) (denote b)
    Embed a -> Embed a
    Combine _ _ b c -> Combine Nothing Nothing (denote b) (denote c)
    CombineTypes _ b c -> CombineTypes Nothing (denote b) (denote c)
    Prefer _ a b c -> Lens.over unsafeSubExpressions denote $ Prefer Nothing a b c
    Record a -> Record $ denoteRecordField <$> a
    RecordLit a -> RecordLit $ denoteRecordField <$> a
    Lam _ a b -> Lam Nothing (denoteFunctionBinding a) (denote b)
    Pi _ t a b -> Pi Nothing t (denote a) (denote b)
    Field a (FieldSelection _ b _) -> Field (denote a) (FieldSelection Nothing b Nothing)
    Equivalent _ a b -> Equivalent Nothing (denote a) (denote b)
    expression -> Lens.over unsafeSubExpressions denote expression
  where
    denoteRecordField (RecordField _ e _ _) = RecordField Nothing (denote e) Nothing Nothing
    denoteBinding (Binding _ c _ d _ e) =
        Binding Nothing c Nothing (fmap denoteBindingAnnotation d) Nothing (denote e)

    denoteBindingAnnotation (_, f) = (Nothing, denote f)

    denoteFunctionBinding (FunctionBinding _ l _ _ t) =
        FunctionBinding Nothing l Nothing Nothing (denote t)

-- | The \"opposite\" of `denote`, like @first absurd@ but faster
renote :: Expr Void a -> Expr s a
renote = unsafeCoerce
{-# INLINE renote #-}

{-| Remove any outermost `Note` constructors

    This is typically used when you want to get the outermost non-`Note`
    constructor without removing internal `Note` constructors
-}
shallowDenote :: Expr s a -> Expr s a
shallowDenote (Note _ e) = shallowDenote e
shallowDenote         e  = e

-- | The set of reserved keywords according to the @keyword@ rule in the grammar
reservedKeywords :: HashSet Text
reservedKeywords =
    Data.HashSet.fromList
        [ "if"
        , "then"
        , "else"
        , "let"
        , "in"
        , "using"
        , "missing"
        , "as"
        , "Infinity"
        , "NaN"
        , "merge"
        , "Some"
        , "toMap"
        , "assert"
        , "forall"
        , "with"
        ]

-- | The set of reserved identifiers for the Dhall language
-- | Contains also all keywords from "reservedKeywords"
reservedIdentifiers :: HashSet Text
reservedIdentifiers = reservedKeywords <>
    Data.HashSet.fromList
        [ -- Builtins according to the `builtin` rule in the grammar
          "Natural/fold"
        , "Natural/build"
        , "Natural/isZero"
        , "Natural/even"
        , "Natural/odd"
        , "Natural/toInteger"
        , "Natural/show"
        , "Natural/subtract"
        , "Integer"
        , "Integer/clamp"
        , "Integer/negate"
        , "Integer/show"
        , "Integer/toDouble"
        , "Integer/show"
        , "Natural/subtract"
        , "Double/show"
        , "List/build"
        , "List/fold"
        , "List/length"
        , "List/head"
        , "List/last"
        , "List/indexed"
        , "List/reverse"
        , "Text/replace"
        , "Text/show"
        , "Bool"
        , "True"
        , "False"
        , "Optional"
        , "None"
        , "Natural"
        , "Integer"
        , "Double"
        , "Text"
        , "Date"
        , "Time"
        , "TimeZone"
        , "List"
        , "Type"
        , "Kind"
        , "Sort"
        ]

-- | Same as @Data.Text.splitOn@, except always returning a `NonEmpty` result
splitOn :: Text -> Text -> NonEmpty Text
splitOn needle haystack =
    case Data.Text.splitOn needle haystack of
        []     -> "" :| []
        t : ts -> t  :| ts

-- | Split `Chunks` by lines
linesLiteral :: Chunks s a -> NonEmpty (Chunks s a)
linesLiteral (Chunks [] suffix) =
    fmap (Chunks []) (splitOn "\n" suffix)
linesLiteral (Chunks ((prefix, interpolation) : pairs₀) suffix₀) =
    foldr
        NonEmpty.cons
        (Chunks ((lastLine, interpolation) : pairs₁) suffix₁ :| chunks)
        (fmap (Chunks []) initLines)
  where
    splitLines = splitOn "\n" prefix

    initLines = NonEmpty.init splitLines
    lastLine  = NonEmpty.last splitLines

    Chunks pairs₁ suffix₁ :| chunks = linesLiteral (Chunks pairs₀ suffix₀)

-- | Flatten several `Chunks` back into a single `Chunks` by inserting newlines
unlinesLiteral :: NonEmpty (Chunks s a) -> Chunks s a
unlinesLiteral chunks =
    Data.Foldable.fold (NonEmpty.intersperse "\n" chunks)

-- | Returns `True` if the `Chunks` represents a blank line
emptyLine :: Chunks s a -> Bool
emptyLine (Chunks [] ""  ) = True
emptyLine (Chunks [] "\r") = True  -- So that `\r\n` is treated as a blank line
emptyLine  _               = False

-- | Return the leading whitespace for a `Chunks` literal
leadingSpaces :: Chunks s a -> Text
leadingSpaces chunks = Data.Text.takeWhile isSpace firstText
  where
    isSpace c = c == ' ' || c == '\t'

    firstText =
        case chunks of
            Chunks                []  suffix -> suffix
            Chunks ((prefix, _) : _ ) _      -> prefix

{-| Compute the longest shared whitespace prefix for the purposes of stripping
    leading indentation
-}
longestSharedWhitespacePrefix :: NonEmpty (Chunks s a) -> Text
longestSharedWhitespacePrefix literals =
    case fmap leadingSpaces filteredLines of
        l : ls -> Data.Foldable.foldl' sharedPrefix l ls
        []     -> ""
  where
    sharedPrefix ab ac =
        case Data.Text.commonPrefixes ab ac of
            Just (a, _b, _c) -> a
            Nothing          -> ""

    -- The standard specifies to filter out blank lines for all lines *except*
    -- for the last line
    filteredLines = newInit <> pure oldLast
      where
        oldInit = NonEmpty.init literals

        oldLast = NonEmpty.last literals

        newInit = filter (not . emptyLine) oldInit

-- | Drop the first @n@ characters for a `Chunks` literal
dropLiteral :: Int -> Chunks s a -> Chunks s a
dropLiteral n (Chunks [] suffix) =
    Chunks [] (Data.Text.drop n suffix)
dropLiteral n (Chunks ((prefix, interpolation) : rest) suffix) =
    Chunks ((Data.Text.drop n prefix, interpolation) : rest) suffix

{-| Convert a single-quoted `Chunks` literal to the equivalent double-quoted
    `Chunks` literal
-}
toDoubleQuoted :: Chunks Src a -> Chunks Src a
toDoubleQuoted literal =
    unlinesLiteral (fmap (dropLiteral indent) literals)
  where
    literals = linesLiteral literal

    longestSharedPrefix = longestSharedWhitespacePrefix literals

    indent = Data.Text.length longestSharedPrefix

{-| `shift` is used by both normalization and type-checking to avoid variable
    capture by shifting variable indices

    For example, suppose that you were to normalize the following expression:

> λ(a : Type) → λ(x : a) → (λ(y : a) → λ(x : a) → y) x

    If you were to substitute @y@ with @x@ without shifting any variable
    indices, then you would get the following incorrect result:

> λ(a : Type) → λ(x : a) → λ(x : a) → x  -- Incorrect normalized form

    In order to substitute @x@ in place of @y@ we need to `shift` @x@ by @1@ in
    order to avoid being misinterpreted as the @x@ bound by the innermost
    lambda.  If we perform that `shift` then we get the correct result:

> λ(a : Type) → λ(x : a) → λ(x : a) → x@1

    As a more worked example, suppose that you were to normalize the following
    expression:

>     λ(a : Type)
> →   λ(f : a → a → a)
> →   λ(x : a)
> →   λ(x : a)
> →   (λ(x : a) → f x x@1) x@1

    The correct normalized result would be:

>     λ(a : Type)
> →   λ(f : a → a → a)
> →   λ(x : a)
> →   λ(x : a)
> →   f x@1 x

    The above example illustrates how we need to both increase and decrease
    variable indices as part of substitution:

    * We need to increase the index of the outer @x\@1@ to @x\@2@ before we
      substitute it into the body of the innermost lambda expression in order
      to avoid variable capture.  This substitution changes the body of the
      lambda expression to @(f x\@2 x\@1)@

    * We then remove the innermost lambda and therefore decrease the indices of
      both @x@s in @(f x\@2 x\@1)@ to @(f x\@1 x)@ in order to reflect that one
      less @x@ variable is now bound within that scope

    Formally, @(shift d (V x n) e)@ modifies the expression @e@ by adding @d@ to
    the indices of all variables named @x@ whose indices are greater than
    @(n + m)@, where @m@ is the number of bound variables of the same name
    within that scope

    In practice, @d@ is always @1@ or @-1@ because we either:

    * increment variables by @1@ to avoid variable capture during substitution
    * decrement variables by @1@ when deleting lambdas after substitution

    @n@ starts off at @0@ when substitution begins and increments every time we
    descend into a lambda or let expression that binds a variable of the same
    name in order to avoid shifting the bound variables by mistake.
-}
shift :: Int -> Var -> Expr s a -> Expr s a
shift d (V x n) (Var (V x' n')) = Var (V x' n'')
  where
    n'' = if x == x' && n <= n' then n' + d else n'
shift d (V x n) (Lam cs (FunctionBinding src0 x' src1 src2 _A) b) =
    Lam cs (FunctionBinding src0 x' src1 src2 _A') b'
  where
    _A' = shift d (V x n ) _A
    b'  = shift d (V x n') b
      where
        n' = if x == x' then n + 1 else n
shift d (V x n) (Pi cs x' _A _B) = Pi cs x' _A' _B'
  where
    _A' = shift d (V x n ) _A
    _B' = shift d (V x n') _B
      where
        n' = if x == x' then n + 1 else n
shift d (V x n) (Let (Binding src0 f src1 mt src2 r) e) =
    Let (Binding src0 f src1 mt' src2 r') e'
  where
    e' = shift d (V x n') e
      where
        n' = if x == f then n + 1 else n

    mt' = fmap (fmap (shift d (V x n))) mt
    r'  =             shift d (V x n)  r
shift d v expression = Lens.over subExpressions (shift d v) expression

-- | Desugar all @with@ expressions
desugarWith :: Expr s a -> Expr s a
desugarWith = Optics.rewriteOf subExpressions rewrite
  where
    rewrite e@(With record (key :| []) value) =
        Just
            (Prefer
                mempty
                (PreferFromWith e)
                record
                (RecordLit [ (key, makeRecordField value) ])
            )
    rewrite e@(With record (key0 :| key1 : keys) value) =
        Just
            (Let
                (makeBinding "_" record)
                (Prefer mempty (PreferFromWith e) "_"
                    (RecordLit
                        [ (key0, makeRecordField $ With (Field "_" (FieldSelection Nothing key0 Nothing)) (key1 :| keys) (shift 1 "_" value)) ]
                    )
                )
            )
    rewrite _ = Nothing

_ERROR :: String
_ERROR = "\ESC[1;31mError\ESC[0m"

{-| Utility function used to throw internal errors that should never happen
    (in theory) but that are not enforced by the type system
-}
internalError :: Data.Text.Text -> forall b . b
internalError text = error (unlines
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
    , Data.Text.unpack text <> "                                                       "
    , "```                                                                             "
    ] )
