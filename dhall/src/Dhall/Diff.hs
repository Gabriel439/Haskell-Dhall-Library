{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards   #-}
{-# LANGUAGE ViewPatterns      #-}
{-# LANGUAGE TypeApplications  #-}

{-| This module provides functionality for concisely displaying the difference
    between two expressions

    For example, this is used in type errors to explain why the actual type does
    not match the expected type
-}

module Dhall.Diff (
    -- * Diff
      Diff (..)
    , diffNormalized
    , diff
    ) where

import Data.Foldable             (fold, toList)
import Data.List.NonEmpty        (NonEmpty (..))
import Data.Monoid               (Any (..))
import Data.Sequence             (Seq)
import Data.String               (IsString (..))
import Data.Text                 (Text)
import Data.Text.Prettyprint.Doc (Doc, Pretty)
import Data.Void                 (Void)
import Dhall.Map                 (Map)
import Dhall.Pretty.Internal     (Ann)
import Dhall.Syntax
    ( Binding (..)
    , Chunks (..)
    , Const (..)
    , DhallDouble (..)
    , Expr (..)
    , FunctionBinding (..)
    , RecordField (..)
    , Var (..)
    )
import Numeric.Natural           (Natural)

import qualified Data.Algorithm.Diff       as Algo.Diff
import qualified Data.List.NonEmpty
import qualified Data.Set
import qualified Data.Text
import qualified Data.Text.Prettyprint.Doc as Pretty
import qualified Data.Time                 as Time
import qualified Dhall.Map
import qualified Dhall.Normalize           as Normalize
import qualified Dhall.Pretty.Internal     as Internal
import qualified Dhall.Syntax              as Syntax

{-| This type is a `Doc` enriched with a `same` flag to efficiently track if
    any difference was detected
-}
data Diff =
    Diff
        { same :: Bool
        , doc  :: Doc Ann
        }

instance Semigroup Diff where
    Diff sameL docL <> Diff sameR docR = Diff (sameL && sameR) (docL <> docR)

instance Monoid (Diff) where
    mempty = Diff {..}
      where
        same = True

        doc = mempty

instance IsString (Diff) where
    fromString string = Diff {..}
      where
        same = True

        doc = fromString string

ignore :: Diff
ignore = "…"

align :: Diff -> Diff
align (Diff {doc = docOld, ..}) = Diff {doc = Pretty.align docOld, .. }

hardline :: Diff
hardline = token Pretty.hardline

minus :: Diff -> Diff
minus l = ("- " <> l) { same = False }

plus :: Diff -> Diff
plus r = ("+ " <> r) { same = False }

difference :: Diff -> Diff -> Diff
difference l r = align (minus l <> hardline <> plus r)

token :: Doc Ann -> Diff
token doc = Diff {..}
  where
    same = True

format :: Diff -> Diff -> Diff
format suffix doc = doc <> (if same doc then suffix else hardline)

builtin :: Doc Ann -> Diff
builtin doc = token (Internal.builtin doc)

keyword :: Doc Ann -> Diff
keyword doc = token (Internal.keyword doc)

operator :: Doc Ann -> Diff
operator doc = token (Internal.operator doc)

colon :: Diff
colon = token Internal.colon

comma :: Diff
comma = token Internal.comma

dot :: Diff
dot = token Internal.dot

equals :: Diff
equals = token Internal.equals

forall :: Diff
forall = token (Internal.forall Internal.Unicode)

lambda :: Diff
lambda = token (Internal.lambda Internal.Unicode)

langle :: Diff
langle = token Internal.langle

lbrace :: Diff
lbrace = token Internal.lbrace

lbracket :: Diff
lbracket = token Internal.lbracket

lparen :: Diff
lparen = token Internal.lparen

pipe :: Diff
pipe = token Internal.pipe

rangle :: Diff
rangle = token Internal.rangle

rarrow :: Diff
rarrow = token (Internal.rarrow Internal.Unicode)

rbrace :: Diff
rbrace = token Internal.rbrace

rbracket :: Diff
rbracket = token Internal.rbracket

rparen :: Diff
rparen = token Internal.rparen

-- | Render the difference between the normal form of two expressions
diffNormalized :: (Eq a, Pretty a) => Expr s a -> Expr s a -> Diff
diffNormalized l0 r0 = Dhall.Diff.diff l1 r1
  where
    l1 = Normalize.alphaNormalize (Normalize.normalize l0)
    r1 = Normalize.alphaNormalize (Normalize.normalize r0)

diffPrimitive :: Eq a => (a -> Diff) -> a -> a -> Diff
diffPrimitive f l r
    | l == r    = ignore
    | otherwise = difference (f l) (f r)

diffLabel :: Text -> Text -> Diff
diffLabel = diffPrimitive (token . Internal.prettyLabel)

diffLabels :: [Text] -> [Text] -> Diff
diffLabels ksL ksR =
    braced (diffFieldNames <> (if anyEqual then [ ignore ] else []))
  where
    setL = Data.Set.fromList ksL
    setR = Data.Set.fromList ksR

    extraL = Data.Set.difference setL setR
    extraR = Data.Set.difference setR setL

    diffFieldNames = foldMap (adapt minus) extraL <> foldMap (adapt plus) extraR
      where
        adapt sign key = [ sign (token (Internal.prettyLabel key)) ]

    anyEqual = not (Data.Set.null (Data.Set.intersection setL setR))

diffNatural :: Natural -> Natural -> Diff
diffNatural = diffPrimitive (token . Internal.prettyNatural)

diffDouble :: DhallDouble -> DhallDouble -> Diff
diffDouble = diffPrimitive (token . Internal.prettyDouble . getDhallDouble)

diffDateLiteral :: Time.Day -> Time.Day -> Diff
diffDateLiteral =
    diffPrimitive (token . Internal.prettyExpr @(Expr Void Void) . DateLiteral)

diffTimeLiteral :: Time.TimeOfDay -> Word -> Time.TimeOfDay -> Word -> Diff
diffTimeLiteral tL pL tR pR =
    diffPrimitive
        (token . Internal.prettyExpr @(Expr Void Void) . uncurry TimeLiteral)
        (tL, pL)
        (tR, pR)

diffTimeZoneLiteral :: Time.TimeZone -> Time.TimeZone -> Diff
diffTimeZoneLiteral =
    diffPrimitive
        (token . Internal.prettyExpr @(Expr Void Void) . TimeZoneLiteral)

diffConst :: Const -> Const -> Diff
diffConst = diffPrimitive (token . Internal.prettyConst)

diffBool :: Bool -> Bool -> Diff
diffBool = diffPrimitive bool
  where
    bool True  = builtin "True"
    bool False = builtin "False"

diffInteger :: Integer -> Integer -> Diff
diffInteger = diffPrimitive (token . Internal.prettyNumber)

diffInt :: Int -> Int -> Diff
diffInt = diffPrimitive (token . Internal.prettyInt)

diffVar :: Var -> Var -> Diff
diffVar (V xL nL) (V xR nR) =
    format mempty label <> if same natural then mempty else "@" <> natural
  where
    label = diffLabel xL xR

    natural = diffInt nL nR

diffPretty :: (Eq a, Pretty a) => a -> a -> Diff
diffPretty = diffPrimitive (token . Pretty.pretty)

diffMaybe :: Diff -> (a -> a -> Diff) -> (Maybe a -> Maybe a -> Diff)
diffMaybe _ _ Nothing Nothing =
    mempty
diffMaybe prefix _ Nothing (Just _) =
    difference mempty (prefix <> ignore)
diffMaybe prefix _ (Just _) Nothing =
    difference (prefix <> ignore) mempty
diffMaybe prefix f (Just l) (Just r) =
    prefix <> f l r

enclosed
    :: Diff
    -> Diff
    -> Diff
    -> [Diff]
    -> Diff
enclosed l _ r []   = l <> r
enclosed l m r docs = align (fold (zipWith (<>) prefixes docs) <> suffix)
  where
    prefixes = l : repeat (hardline <> m)

    suffix = hardline <> r

enclosed'
    :: Diff
    -> Diff
    -> NonEmpty (Diff)
    -> Diff
enclosed' l m docs =
    align (fold (Data.List.NonEmpty.zipWith (<>) prefixes docs))
  where
    prefixes = l :| repeat (hardline <> m)

diffKeyVals
    :: (Eq a, Pretty a)
    => Diff
    -> Map Text (RecordField Void a)
    -> Map Text (RecordField Void a)
    -> [Diff]
diffKeyVals assign kvsL kvsR = diffKeysWith assign diff
    (recordFieldValue <$> kvsL)
    (recordFieldValue <$> kvsR)

diffKeysWith
    :: Diff
    -> (a -> a -> Diff)
    -> Map Text a
    -> Map Text a
    -> [Diff]
diffKeysWith assign diffVals kvsL kvsR =
    diffFieldNames <> diffFieldValues <> (if anyEqual then [ ignore ] else [])
  where
    ksL = Dhall.Map.keysSet kvsL
    ksR = Dhall.Map.keysSet kvsR

    extraL = Data.Set.difference ksL ksR
    extraR = Data.Set.difference ksR ksL

    diffFieldNames = foldMap (adapt minus) extraL <> foldMap (adapt plus) extraR
      where
        adapt sign key =
            [   sign (token (Internal.prettyLabel key))
            <>  " "
            <>  assign
            <>  " "
            <>  ignore
            ]

    shared = Dhall.Map.intersectionWith diffVals kvsL kvsR

    diffFieldValues =
        filter (not . same) (Dhall.Map.foldMapWithKey adapt shared)
      where
        adapt key doc =
            [   (if ksL == ksR then mempty else "  ")
            <>  token (Internal.prettyLabel key)
            <>  " "
            <>  assign
            <>  " "
            <>  doc
            ]

    anyEqual = getAny (foldMap (Any . same) shared)

braced :: [Diff] -> Diff
braced = enclosed (lbrace <> " ") (comma <> " ") rbrace

angled :: [Diff] -> Diff
angled = enclosed (langle <> " ") (pipe <> " ") rangle

bracketed :: [Diff] -> Diff
bracketed = enclosed (lbracket <> " ") (comma <> " ") rbracket

diffText :: Text -> Text -> Diff
diffText l r = "\"" <> foldMap prettyPart parts <> "\""
  where
    -- TODO: check for color support from the TTY
    colorDiff colorCode chars =
            "\ESC["
        <>  colorCode
        <>  "m"
        <>  fromString chars
        <>  "\ESC[0m"

    prettyPart part =
      case part of
        -- Only present in left
        Algo.Diff.First  chars ->
            -- Red background
            (colorDiff "41" chars) { same = False }

        -- Only present in right
        Algo.Diff.Second chars ->
            -- Green background
            (colorDiff "42" chars) { same = False }

        -- Present in both
        Algo.Diff.Both _ chars ->
            -- Dim foreground
            colorDiff "2" chars

    parts = Algo.Diff.getGroupedDiff (Data.Text.unpack l) (Data.Text.unpack r)

diffChunks
    :: (Eq a, Pretty a)
    => Chunks Void a -> Chunks Void a -> Diff
diffChunks cL cR
  | null chunks             = "\"\""
  | [c] <- chunks           = c
  | otherwise               = align (enclosed "   " "++ " "" chunks)
  where
    toEitherList (Chunks te t) =
        concatMap (\(a, b) -> [Left a, Right b]) te ++ [Left t]

    diffTextSkeleton = difference textSkeleton textSkeleton

    chunks = zipWith chunkDiff (toEitherList cL) (toEitherList cR)

    chunkDiff a b =
      case (a, b) of
        (Left  x, Left y ) -> diffText x y
        (Right x, Right y) -> diff x y
        _                  -> diffTextSkeleton

diffList
    :: (Eq a, Pretty a)
    => Seq (Expr Void a) -> Seq (Expr Void a) -> Diff
diffList l r = bracketed (loop parts₀)
  where
    -- Sections of the list that are only in left, only in right, or in both
    parts₀ = Algo.Diff.getGroupedDiffBy equal (toList l) (toList r)

    equal a b = same (diff a b)

    -- Render each element of a list using an extra rendering function f
    prettyElems f = map (f . token . Internal.prettyExpr)

    loop [] =
        mempty
    loop (Algo.Diff.First as : Algo.Diff.Second bs : parts)
        | length as == length bs = zipWith diff as bs <> loop parts
    loop (part : parts) =
        diffPart part <> loop parts

    diffPart part =
      case part of
        -- Only present in left
        Algo.Diff.First  elements ->
            prettyElems minus elements

        -- Only present in right
        Algo.Diff.Second elements ->
            prettyElems plus  elements

        -- Present in both
        Algo.Diff.Both _ _        ->
            pure ignore

diffRecord
    :: (Eq a, Pretty a)
    => Map Text (RecordField Void a) -> Map Text (RecordField Void a) -> Diff
diffRecord kvsL kvsR = braced (diffKeyVals colon kvsL kvsR)

diffRecordLit
    :: (Eq a, Pretty a)
    => Map Text (RecordField Void a) -> Map Text (RecordField Void a) -> Diff
diffRecordLit kvsL kvsR = braced (diffKeyVals equals kvsL kvsR)

diffUnion
    :: (Eq a, Pretty a)
    => Map Text (Maybe (Expr Void a)) -> Map Text (Maybe (Expr Void a)) -> Diff
diffUnion kvsL kvsR = angled (diffKeysWith colon diffVals kvsL kvsR)
  where
    diffVals = diffMaybe (colon <> " ") diff

textSkeleton :: Diff
textSkeleton =
        "\""
    <>  ignore
    <>  "\""

skeleton :: Pretty a => Expr s a -> Diff
skeleton (Lam {}) =
        lambda
    <>  lparen
    <>  ignore
    <>  " "
    <>  colon
    <>  " "
    <>  ignore
    <>  rparen
    <>  " "
    <>  rarrow
    <>  " "
    <>  ignore
    <> " (a function)"
skeleton (Pi {}) =
        ignore
    <>  " "
    <>  rarrow
    <>  " "
    <>  ignore
    <> " (a function type)"
skeleton (App Optional _) =
        "Optional "
    <>  ignore
skeleton (App None _) =
        "None "
    <>  ignore
skeleton (Some _) =
        "Some "
    <>  ignore
skeleton (App List _) =
        "List "
    <>  ignore
skeleton (App {}) =
        ignore
    <>  " "
    <>  ignore
skeleton (Let {}) =
        keyword "let"
    <>  " "
    <>  ignore
    <>  " "
    <>  equals
    <>  " "
    <>  ignore
    <>  " "
    <>  keyword "in"
    <>  " "
    <>  ignore
skeleton (Annot {}) =
        ignore
    <>  " "
    <>  colon
    <>  " "
    <>  ignore
skeleton (BoolAnd {}) =
        ignore
    <>  " "
    <>  operator "&&"
    <>  " "
    <>  ignore
skeleton (BoolOr {}) =
        ignore
    <>  " "
    <>  operator "||"
    <>  " "
    <>  ignore
skeleton (BoolEQ {}) =
        ignore
    <>  " "
    <>  operator "=="
    <>  " "
    <>  ignore
skeleton (BoolNE {}) =
        ignore
    <>  " "
    <>  operator "!="
    <>  " "
    <>  ignore
skeleton (BoolIf {}) =
        keyword "if"
    <>  " "
    <>  ignore
    <>  " "
    <>  keyword "then"
    <>  " "
    <>  ignore
    <>  " "
    <>  keyword "else"
    <>  " "
    <>  ignore
skeleton (NaturalPlus {}) =
        ignore
    <>  " "
    <>  operator "+"
    <>  " "
    <>  ignore
skeleton (NaturalTimes {}) =
        ignore
    <>  " "
    <>  operator "*"
    <>  " "
    <>  ignore
skeleton (TextLit {}) =
        textSkeleton
skeleton (TextAppend {}) =
        ignore
    <>  " "
    <>  operator "++"
    <>  " "
    <>  ignore
skeleton (ListLit _ elems)
    | null elems =
            lbracket
        <>  rbracket
        <>  " "
        <>  colon
        <>  " "
        <>  ignore
    | otherwise =
            lbracket
        <>  " "
        <>  ignore
        <>  " "
        <>  rbracket
skeleton (ListAppend {}) =
        ignore
    <>  " "
    <>  operator "#"
    <>  " "
    <>  ignore
skeleton (Record {}) =
        lbrace
    <>  " "
    <>  ignore
    <>  " "
    <>  colon
    <>  " "
    <>  ignore
    <>  " "
    <>  rbrace
    <>  " (a record type)"
skeleton (RecordLit {}) =
        lbrace
    <>  " "
    <>  ignore
    <>  " "
    <>  equals
    <>  " "
    <>  ignore
    <>  " "
    <>  rbrace
    <> " (a record)"
skeleton (Union {}) =
        langle
    <>  " "
    <>  ignore
    <>  " "
    <>  colon
    <>  " "
    <>  ignore
    <>  " "
    <>  rangle
    <> " (a union type)"
skeleton (Combine {}) =
        ignore
    <>  " "
    <>  operator "∧"
    <>  " "
    <>  ignore
skeleton (CombineTypes {}) =
        ignore
    <>  " "
    <>  operator "⩓"
    <>  " "
    <>  ignore
skeleton (Prefer {}) =
        ignore
    <>  " "
    <>  operator "⫽"
    <>  " "
    <>  ignore
skeleton (RecordCompletion {}) =
        ignore
    <>  operator "::"
    <>  ignore
skeleton (Merge {}) =
        keyword "merge"
    <>  " "
    <>  ignore
    <>  " "
    <>  ignore
skeleton (ToMap {}) =
        keyword "toMap"
    <>  " "
    <>  ignore
skeleton (Field {}) =
        ignore
    <>  dot
    <>  ignore
skeleton (Project {}) =
        ignore
    <>  dot
    <>  lbrace
    <>  " "
    <>  ignore
    <>  " "
    <>  rbrace
skeleton (With {}) =
         ignore
    <>   " "
    <>   keyword "with"
    <>   " "
    <>   ignore
skeleton x = token (Pretty.pretty x)

mismatch :: Pretty a => Expr s a -> Expr s a -> Diff
mismatch l r = difference (skeleton l) (skeleton r)

-- | Render the difference between two expressions
diff :: (Eq a, Pretty a) => Expr Void a -> Expr Void a -> Diff
diff l@(Lam {}) r@(Lam {}) =
    enclosed' "  " (rarrow <> " ") (docs l r)
  where
    docs
        (Lam _ (FunctionBinding { functionBindingVariable = aL, functionBindingAnnotation = bL }) cL)
        (Lam _ (FunctionBinding { functionBindingVariable = aR, functionBindingAnnotation = bR }) cR) =
        Data.List.NonEmpty.cons (align doc) (docs cL cR)
      where
        doc =   lambda
            <>  lparen
            <>  format " " (diffLabel aL aR)
            <>  colon
            <>  " "
            <>  format mempty (diff bL bR)
            <>  rparen

    docs aL aR =
        pure (diff aL aR)
diff l@(Lam {}) r =
    mismatch l r
diff l r@(Lam {}) =
    mismatch l r
diff l@(BoolIf {}) r@(BoolIf {}) =
    enclosed' "      " (keyword "else" <> "  ") (docs l r)
  where
    docs (BoolIf aL bL cL) (BoolIf aR bR cR) =
        Data.List.NonEmpty.cons (align doc) (docs cL cR)
      where
        doc =   keyword "if"
            <>  " "
            <>  format " " (diff aL aR)
            <>  keyword "then"
            <>  " "
            <>  diff bL bR
    docs aL aR =
        pure (diff aL aR)
diff l@(BoolIf {}) r =
    mismatch l r
diff l r@(BoolIf {}) =
    mismatch l r
diff l@(Let {}) r@(Let {}) =
    enclosed' "    " (keyword "in" <> "  ") (docs l r)
  where
    docs (Let (Binding _ aL _ bL _ cL) dL) (Let (Binding _ aR _ bR _ cR) dR) =
        Data.List.NonEmpty.cons (align doc) (docs dL dR)
      where
        bL' = fmap snd bL
        bR' = fmap snd bR

        doc =   keyword "let"
            <>  " "
            <>  format " " (diffLabel aL aR)
            <>  format " " (diffMaybe (colon <> " ") diff bL' bR')
            <>  equals
            <>  " "
            <>  diff cL cR
    docs aL aR = pure (diff aL aR)
diff l@(Let {}) r =
    mismatch l r
diff l r@(Let {}) =
    mismatch l r
diff l@(Pi {}) r@(Pi {}) =
    enclosed' "  " (rarrow <> " ") (docs l r)
  where
    docs (Pi _ aL bL cL) (Pi _ aR bR cR) =
        Data.List.NonEmpty.cons (align doc) (docs cL cR)
      where
        doc | same docA && same docB = ignore
            | same docA =
                format mempty docB
            | otherwise =
                    forall
                <>  lparen
                <>  format " " docA
                <>  colon
                <>  " "
                <>  format mempty docB
                <>  rparen
          where
            docA = diffLabel aL aR

            docB = diff bL bR

    docs aL aR = pure (diff aL aR)
diff l@(Pi {}) r =
    mismatch l r
diff l r@(Pi {}) =
    mismatch l r
diff (Assert aL) (Assert aR) =
    align
        (  "  " <> keyword "assert"
        <> hardline <> colon <> " " <> diff aL aR
        )
diff l@(Assert {}) r =
    mismatch l r
diff l r@(Assert {}) =
    mismatch l r
diff l r =
    diffAnnotatedExpression l r

diffAnnotatedExpression :: (Eq a, Pretty a) => Expr Void a -> Expr Void a -> Diff
diffAnnotatedExpression (Merge aL bL cL) (Merge aR bR cR) = align doc
  where
    doc =   keyword "merge"
        <>  " "
        <>  format " " (diffWithExpression aL aR)
        <>  format " " (diffWithExpression bL bR)
        <>  diffMaybe (colon <> " ") diffApplicationExpression cL cR
diffAnnotatedExpression l@(Merge {}) r =
    mismatch l r
diffAnnotatedExpression l r@(Merge {}) =
    mismatch l r
diffAnnotatedExpression (ToMap aL bL) (ToMap aR bR) = align doc
  where
    doc =   keyword "toMap"
        <>  " "
        <>  format " " (diffWithExpression aL aR)
        <>  diffMaybe (colon <> " ") diffApplicationExpression bL bR
diffAnnotatedExpression l@(ToMap {}) r =
    mismatch l r
diffAnnotatedExpression l r@(ToMap {}) =
    mismatch l r
diffAnnotatedExpression (ListLit aL@(Just _) bL) (ListLit aR bR) = align doc
  where
    doc =   format " " (diffList bL bR)
        <>  format " " (diffMaybe (colon <> " ") diffApplicationExpression aL aR)
diffAnnotatedExpression (ListLit aL bL) (ListLit aR@(Just _) bR) = align doc
  where
    doc =   format " " (diffList bL bR)
        <>  format " " (diffMaybe (colon <> " ") diffApplicationExpression aL aR)
diffAnnotatedExpression l@(Annot {}) r@(Annot {}) =
    enclosed' "  " (colon <> " ") (docs l r)
  where
    docs (Annot aL bL) (Annot aR bR) =
        Data.List.NonEmpty.cons (align doc) (docs bL bR)
      where
        doc = diffOperatorExpression aL aR
    docs aL aR =
        diff aL aR :| []
diffAnnotatedExpression l@(Annot {}) r =
    mismatch l r
diffAnnotatedExpression l r@(Annot {}) =
    mismatch l r
diffAnnotatedExpression l r =
    diffOperatorExpression l r

{- Whitespace in diffs of operator expressions:

All indentation (whether pretty-printing or diffing) is a multiple of two
spaces, so if the operator is one character long (like ?) then the diff pads
the left margin to two space:

    ␣␣e₀
    ?␣e₁

... but if the operator is two characters long (like ||) then the diff pads
the left margin to four spaces:

     ␣␣␣␣e₀
     ||␣␣e₁
-}
diffOperatorExpression :: (Eq a, Pretty a) => Expr Void a -> Expr Void a -> Diff
diffOperatorExpression = diffImportAltExpression

diffImportAltExpression :: (Pretty a, Eq a) => Expr Void a -> Expr Void a -> Diff
diffImportAltExpression l@(ImportAlt {}) r@(ImportAlt {}) =
    enclosed' "  " (operator "?" <> " ") (docs l r)
  where
    docs (ImportAlt aL bL) (ImportAlt aR bR) =
        Data.List.NonEmpty.cons (diffOrExpression aL aR) (docs bL bR)
    docs aL aR =
        pure (diffOrExpression aL aR)
diffImportAltExpression l@(ImportAlt {}) r =
    mismatch l r
diffImportAltExpression l r@(ImportAlt {}) =
    mismatch l r
diffImportAltExpression l r =
    diffOrExpression l r

diffOrExpression :: (Eq a, Pretty a) => Expr Void a -> Expr Void a -> Diff
diffOrExpression l@(BoolOr {}) r@(BoolOr {}) =
    enclosed' "    " (operator "||" <> "  ") (docs l r)
  where
    docs (BoolOr aL bL) (BoolOr aR bR) =
        Data.List.NonEmpty.cons (diffPlusExpression aL aR) (docs bL bR)
    docs aL aR =
        pure (diffPlusExpression aL aR)
diffOrExpression l@(BoolOr {}) r =
    mismatch l r
diffOrExpression l r@(BoolOr {}) =
    mismatch l r
diffOrExpression l r =
    diffPlusExpression l r

diffPlusExpression :: (Eq a, Pretty a) => Expr Void a -> Expr Void a -> Diff
diffPlusExpression l@(NaturalPlus {}) r@(NaturalPlus {}) =
    enclosed' "  " (operator "+" <> " ") (docs l r)
  where
    docs (NaturalPlus aL bL) (NaturalPlus aR bR) =
        Data.List.NonEmpty.cons (diffTextAppendExpression aL aR) (docs bL bR)
    docs aL aR =
        pure (diffTextAppendExpression aL aR)
diffPlusExpression l@(NaturalPlus {}) r =
    mismatch l r
diffPlusExpression l r@(NaturalPlus {}) =
    mismatch l r
diffPlusExpression l r =
    diffTextAppendExpression l r

diffTextAppendExpression :: (Eq a, Pretty a) => Expr Void a -> Expr Void a -> Diff
diffTextAppendExpression l@(TextAppend {}) r@(TextAppend {}) =
    enclosed' "    " (operator "++" <> "  ") (docs l r)
  where
    docs (TextAppend aL bL) (TextAppend aR bR) =
        Data.List.NonEmpty.cons (diffListAppendExpression aL aR) (docs bL bR)
    docs aL aR =
        pure (diffListAppendExpression aL aR)
diffTextAppendExpression l@(TextAppend {}) r =
    mismatch l r
diffTextAppendExpression l r@(TextAppend {}) =
    mismatch l r
diffTextAppendExpression l r =
    diffListAppendExpression l r

diffListAppendExpression :: (Eq a, Pretty a) => Expr Void a -> Expr Void a -> Diff
diffListAppendExpression l@(ListAppend {}) r@(ListAppend {}) =
    enclosed' "  " (operator "#" <> " ") (docs l r)
  where
    docs (ListAppend aL bL) (ListAppend aR bR) =
        Data.List.NonEmpty.cons (diffAndExpression aL aR) (docs bL bR)
    docs aL aR =
        pure (diffAndExpression aL aR)
diffListAppendExpression l@(ListAppend {}) r =
    mismatch l r
diffListAppendExpression l r@(ListAppend {}) =
    mismatch l r
diffListAppendExpression l r =
    diffAndExpression l r

diffAndExpression :: (Eq a, Pretty a) => Expr Void a -> Expr Void a -> Diff
diffAndExpression l@(BoolAnd {}) r@(BoolAnd {}) =
    enclosed' "    " (operator "&&" <> "  ") (docs l r)
  where
    docs (BoolAnd aL bL) (BoolAnd aR bR) =
        Data.List.NonEmpty.cons (diffCombineExpression aL aR) (docs bL bR)
    docs aL aR =
        pure (diffCombineExpression aL aR)
diffAndExpression l@(BoolAnd {}) r =
    mismatch l r
diffAndExpression l r@(BoolAnd {}) =
    mismatch l r
diffAndExpression l r =
    diffCombineExpression l r

diffCombineExpression :: (Eq a, Pretty a) => Expr Void a -> Expr Void a -> Diff
diffCombineExpression l@(Combine {}) r@(Combine {}) =
    enclosed' "  " (operator "∧" <> " ") (docs l r)
  where
    docs (Combine _ _ aL bL) (Combine _ _ aR bR) =
        Data.List.NonEmpty.cons (diffPreferExpression aL aR) (docs bL bR)
    docs aL aR =
        pure (diffPreferExpression aL aR)
diffCombineExpression l@(Combine {}) r =
    mismatch l r
diffCombineExpression l r@(Combine {}) =
    mismatch l r
diffCombineExpression l r =
    diffPreferExpression l r

diffPreferExpression :: (Eq a, Pretty a) => Expr Void a -> Expr Void a -> Diff
diffPreferExpression l@(Prefer {}) r@(Prefer {}) =
    enclosed' "  " (operator "⫽" <> " ") (docs l r)
  where
    docs (Prefer _ _ aL bL) (Prefer _ _ aR bR) =
        Data.List.NonEmpty.cons (diffCombineTypesExpression aL aR) (docs bL bR)
    docs aL aR =
        pure (diffCombineTypesExpression aL aR)
diffPreferExpression l@(Prefer {}) r =
    mismatch l r
diffPreferExpression l r@(Prefer {}) =
    mismatch l r
diffPreferExpression l r =
    diffCombineTypesExpression l r

diffCombineTypesExpression :: (Eq a, Pretty a) => Expr Void a -> Expr Void a -> Diff
diffCombineTypesExpression l@(CombineTypes {}) r@(CombineTypes {}) =
    enclosed' "  " (operator "*" <> " ") (docs l r)
  where
    docs (CombineTypes _ aL bL) (CombineTypes _ aR bR) =
        Data.List.NonEmpty.cons (diffTimesExpression aL aR) (docs bL bR)
    docs aL aR =
        pure (diffTimesExpression aL aR)
diffCombineTypesExpression l@(CombineTypes {}) r =
    mismatch l r
diffCombineTypesExpression l r@(CombineTypes {}) =
    mismatch l r
diffCombineTypesExpression l r =
    diffTimesExpression l r

diffTimesExpression :: (Eq a, Pretty a) => Expr Void a -> Expr Void a -> Diff
diffTimesExpression l@(NaturalTimes {}) r@(NaturalTimes {}) =
    enclosed' "  " (operator "*" <> " ") (docs l r)
  where
    docs (NaturalTimes aL bL) (NaturalTimes aR bR) =
        Data.List.NonEmpty.cons (diffEqualExpression aL aR) (docs bL bR)
    docs aL aR =
        pure (diffEqualExpression aL aR)
diffTimesExpression l@(NaturalTimes {}) r =
    mismatch l r
diffTimesExpression l r@(NaturalTimes {}) =
    mismatch l r
diffTimesExpression l r =
    diffEqualExpression l r

diffEqualExpression :: (Eq a, Pretty a) => Expr Void a -> Expr Void a -> Diff
diffEqualExpression l@(BoolEQ {}) r@(BoolEQ {}) =
    enclosed' "    " (operator "==" <> "  ") (docs l r)
  where
    docs (BoolEQ aL bL) (BoolEQ aR bR) =
        Data.List.NonEmpty.cons (diffNotEqualExpression aL aR) (docs bL bR)
    docs aL aR =
        pure (diffNotEqualExpression aL aR)
diffEqualExpression l@(BoolEQ {}) r =
    mismatch l r
diffEqualExpression l r@(BoolEQ {}) =
    mismatch l r
diffEqualExpression l r =
    diffNotEqualExpression l r

diffNotEqualExpression :: (Eq a, Pretty a) => Expr Void a -> Expr Void a -> Diff
diffNotEqualExpression l@(BoolNE {}) r@(BoolNE {}) =
    enclosed' "    " (operator "!=" <> "  ") (docs l r)
  where
    docs (BoolNE aL bL) (BoolNE aR bR) =
        Data.List.NonEmpty.cons (diffEquivalentExpression aL aR) (docs bL bR)
    docs aL aR =
        pure (diffEquivalentExpression aL aR)
diffNotEqualExpression l@(BoolNE {}) r =
    mismatch l r
diffNotEqualExpression l r@(BoolNE {}) =
    mismatch l r
diffNotEqualExpression l r =
    diffEquivalentExpression l r

diffEquivalentExpression
    :: (Eq a, Pretty a) => Expr Void a -> Expr Void a -> Diff
diffEquivalentExpression l@(Equivalent {}) r@(Equivalent {}) =
    enclosed' "  " (operator "≡" <> " ") (docs l r)
  where
    docs (Equivalent _ aL bL) (Equivalent _ aR bR) =
        Data.List.NonEmpty.cons (diffApplicationExpression aL aR) (docs bL bR)
    docs aL aR =
        pure (diffApplicationExpression aL aR)
diffEquivalentExpression l@(Equivalent {}) r =
    mismatch l r
diffEquivalentExpression l r@(Equivalent {}) =
    mismatch l r
diffEquivalentExpression l r =
    diffApplicationExpression l r

diffApplicationExpression :: (Eq a, Pretty a) => Expr Void a -> Expr Void a -> Diff
diffApplicationExpression l@(App {}) r@(App {}) =
    enclosed' mempty mempty (Data.List.NonEmpty.reverse (docs l r))
  where
    docs (App aL bL) (App aR bR) =
        Data.List.NonEmpty.cons (diffWithExpression bL bR) (docs aL aR)
    docs (Some aL) (Some aR) =
        diffWithExpression aL aR :| [ builtin "Some" ]
    docs aL aR@(Some {}) =
        pure (mismatch aL aR)
    docs aL@(Some {}) aR =
        pure (mismatch aL aR)
    docs aL aR =
        pure (diffWithExpression aL aR)
diffApplicationExpression l@(App {}) r =
    mismatch l r
diffApplicationExpression l r@(App {}) =
    mismatch l r
diffApplicationExpression (Some l) (Some r) =
    enclosed' mempty mempty (builtin "Some" :| [ diffWithExpression l r ])
diffApplicationExpression l@(Some {}) r =
    mismatch l r
diffApplicationExpression l r@(Some {}) =
    mismatch l r
diffApplicationExpression l r =
    diffWithExpression l r

diffWithExpression :: (Eq a, Pretty a) => Expr Void a -> Expr Void a -> Diff
diffWithExpression (With eL ksL vL) (With eR ksR vR) =
    align
        (   format " " (diffImportExpression eL eR)
        <>  "with "
        <>  align
            (   format " " (diffPath ksL ksR)
            <>  "= "
            <>  diffOperatorExpression vL vR
            )
        )
  where
    diffPath (kL :| []) (kR :| []) =
        diffLabel kL kR
    diffPath (kL₀ :| kL₁ : ksL') (kR₀ :| kR₁ : ksR') =
            format "" (diffLabel kL₀ kR₀)
        <>  dot
        <>  diffPath (kL₁ :| ksL') (kR₁ :| ksR')
    diffPath (kL :| []) (kR₀ :| kR₁ : ksR') =
            format "" (diffLabel kL kR₀)
        <>  plus (foldMap (\k -> dot <> token (Internal.prettyLabel k)) (kR₁ :| ksR'))
    diffPath (kL₀ :| kL₁ : ksL') (kR :| []) =
            format "" (diffLabel kL₀ kR)
        <>  minus (foldMap (\k -> dot <> token (Internal.prettyLabel k)) (kL₁ :| ksL'))
diffWithExpression l r@With{} =
    mismatch l r
diffWithExpression l@With{} r =
    mismatch l r
diffWithExpression l r =
    diffImportExpression l r

diffImportExpression :: (Eq a, Pretty a) => Expr Void a -> Expr Void a -> Diff
diffImportExpression (Embed l) (Embed r) =
    diffPretty l r
diffImportExpression l@(Embed {}) r =
    mismatch l r
diffImportExpression l r@(Embed {}) =
    mismatch l r
diffImportExpression l r =
    diffRecordCompletionExpression l r

diffRecordCompletionExpression :: (Eq a, Pretty a) => Expr Void a -> Expr Void a -> Diff
diffRecordCompletionExpression (RecordCompletion aL bL) (RecordCompletion aR bR) =
       diffSelectorExpression aL aR <> "::" <> diffSelectorExpression bL bR
diffRecordCompletionExpression l@(RecordCompletion {}) r =
    mismatch l r
diffRecordCompletionExpression l r@(RecordCompletion {}) =
    mismatch l r
diffRecordCompletionExpression l r =
    diffSelectorExpression l r

diffSelectorExpression :: (Eq a, Pretty a) => Expr Void a -> Expr Void a -> Diff
diffSelectorExpression l@(Field {}) r@(Field {}) =
    enclosed' "  " (dot <> " ") (Data.List.NonEmpty.reverse (docs l r))
  where
    docs (Field aL (Syntax.fieldSelectionLabel -> bL)) (Field aR (Syntax.fieldSelectionLabel -> bR)) =
        Data.List.NonEmpty.cons (diffLabel bL bR) (docs aL aR)
    docs (Project aL (Left bL)) (Project aR (Left bR)) =
        Data.List.NonEmpty.cons (diffLabels bL bR) (docs aL aR)
    docs (Project aL (Right bL)) (Project aR (Right bR)) =
        Data.List.NonEmpty.cons (diff bL bR) (docs aL aR)
    docs aL aR =
        pure (diffPrimitiveExpression aL aR)
diffSelectorExpression l@(Field {}) r =
    mismatch l r
diffSelectorExpression l r@(Field {}) =
    mismatch l r
diffSelectorExpression l@(Project {}) r@(Project {}) =
    enclosed' "  " (dot <> " ") (Data.List.NonEmpty.reverse (docs l r))
  where
    docs (Field aL (Syntax.fieldSelectionLabel -> bL)) (Field aR (Syntax.fieldSelectionLabel ->bR)) =
        Data.List.NonEmpty.cons (diffLabel bL bR) (docs aL aR)
    docs (Project aL (Left bL)) (Project aR (Left bR)) =
        Data.List.NonEmpty.cons (diffLabels bL bR) (docs aL aR)
    docs (Project aL (Right bL)) (Project aR (Right bR)) =
        Data.List.NonEmpty.cons (diff bL bR) (docs aL aR)
    docs aL aR =
        pure (diffPrimitiveExpression aL aR)
diffSelectorExpression l@(Project {}) r =
    mismatch l r
diffSelectorExpression l r@(Project {}) =
    mismatch l r
diffSelectorExpression l r =
    diffPrimitiveExpression l r

diffPrimitiveExpression :: (Eq a, Pretty a) => Expr Void a -> Expr Void a -> Diff
diffPrimitiveExpression (Var aL) (Var aR) =
    diffVar aL aR
diffPrimitiveExpression l@(Var {}) r =
    mismatch l r
diffPrimitiveExpression l r@(Var {}) =
    mismatch l r
diffPrimitiveExpression (Const aL) (Const aR) =
    diffConst aL aR
diffPrimitiveExpression l@(Const {}) r =
    mismatch l r
diffPrimitiveExpression l r@(Const {}) =
    mismatch l r
diffPrimitiveExpression Bool Bool =
    "…"
diffPrimitiveExpression l@Bool r =
    mismatch l r
diffPrimitiveExpression l r@Bool =
    mismatch l r
diffPrimitiveExpression Natural Natural =
    "…"
diffPrimitiveExpression l@Natural r =
    mismatch l r
diffPrimitiveExpression l r@Natural =
    mismatch l r
diffPrimitiveExpression NaturalFold NaturalFold =
    "…"
diffPrimitiveExpression l@NaturalFold r =
    mismatch l r
diffPrimitiveExpression l r@NaturalFold =
    mismatch l r
diffPrimitiveExpression NaturalBuild NaturalBuild =
    "…"
diffPrimitiveExpression l@NaturalBuild r =
    mismatch l r
diffPrimitiveExpression l r@NaturalBuild =
    mismatch l r
diffPrimitiveExpression NaturalIsZero NaturalIsZero =
    "…"
diffPrimitiveExpression l@NaturalIsZero r =
    mismatch l r
diffPrimitiveExpression l r@NaturalIsZero =
    mismatch l r
diffPrimitiveExpression NaturalEven NaturalEven =
    "…"
diffPrimitiveExpression l@NaturalEven r =
    mismatch l r
diffPrimitiveExpression l r@NaturalEven =
    mismatch l r
diffPrimitiveExpression NaturalOdd NaturalOdd =
    "…"
diffPrimitiveExpression l@NaturalOdd r =
    mismatch l r
diffPrimitiveExpression l r@NaturalOdd =
    mismatch l r
diffPrimitiveExpression NaturalToInteger NaturalToInteger =
    "…"
diffPrimitiveExpression l@NaturalToInteger r =
    mismatch l r
diffPrimitiveExpression l r@NaturalToInteger =
    mismatch l r
diffPrimitiveExpression NaturalShow NaturalShow =
    "…"
diffPrimitiveExpression l@NaturalShow r =
    mismatch l r
diffPrimitiveExpression l r@NaturalShow =
    mismatch l r
diffPrimitiveExpression NaturalSubtract NaturalSubtract =
    "…"
diffPrimitiveExpression l@NaturalSubtract r =
    mismatch l r
diffPrimitiveExpression l r@NaturalSubtract =
    mismatch l r
diffPrimitiveExpression Integer Integer =
    "…"
diffPrimitiveExpression l@Integer r =
    mismatch l r
diffPrimitiveExpression l r@Integer =
    mismatch l r
diffPrimitiveExpression IntegerClamp IntegerClamp =
    "…"
diffPrimitiveExpression l@IntegerClamp r =
    mismatch l r
diffPrimitiveExpression l r@IntegerClamp =
    mismatch l r
diffPrimitiveExpression IntegerNegate IntegerNegate =
    "…"
diffPrimitiveExpression l@IntegerNegate r =
    mismatch l r
diffPrimitiveExpression l r@IntegerNegate =
    mismatch l r
diffPrimitiveExpression IntegerShow IntegerShow =
    "…"
diffPrimitiveExpression l@IntegerShow r =
    mismatch l r
diffPrimitiveExpression l r@IntegerShow =
    mismatch l r
diffPrimitiveExpression IntegerToDouble IntegerToDouble =
    "…"
diffPrimitiveExpression l@IntegerToDouble r =
    mismatch l r
diffPrimitiveExpression l r@IntegerToDouble =
    mismatch l r
diffPrimitiveExpression Double Double =
    "…"
diffPrimitiveExpression l@Double r =
    mismatch l r
diffPrimitiveExpression l r@Double =
    mismatch l r
diffPrimitiveExpression DoubleShow DoubleShow =
    "…"
diffPrimitiveExpression l@DoubleShow r =
    mismatch l r
diffPrimitiveExpression l r@DoubleShow =
    mismatch l r
diffPrimitiveExpression Text Text =
    "…"
diffPrimitiveExpression l@Text r =
    mismatch l r
diffPrimitiveExpression l r@Text =
    mismatch l r
diffPrimitiveExpression TextReplace TextReplace =
    "…"
diffPrimitiveExpression l@TextReplace r =
    mismatch l r
diffPrimitiveExpression l r@TextReplace =
    mismatch l r
diffPrimitiveExpression TextShow TextShow =
    "…"
diffPrimitiveExpression l@TextShow r =
    mismatch l r
diffPrimitiveExpression l r@TextShow =
    mismatch l r
diffPrimitiveExpression Date Date =
    "…"
diffPrimitiveExpression l r@Date =
    mismatch l r
diffPrimitiveExpression l@Date r=
    mismatch l r
diffPrimitiveExpression Time Time =
    "…"
diffPrimitiveExpression l r@Time =
    mismatch l r
diffPrimitiveExpression l@Time r=
    mismatch l r
diffPrimitiveExpression TimeZone TimeZone =
    "…"
diffPrimitiveExpression l r@TimeZone =
    mismatch l r
diffPrimitiveExpression l@TimeZone r=
    mismatch l r
diffPrimitiveExpression List List =
    "…"
diffPrimitiveExpression l@List r =
    mismatch l r
diffPrimitiveExpression l r@List =
    mismatch l r
diffPrimitiveExpression (ListLit Nothing bL) (ListLit Nothing bR) = align doc
  where
    doc = format " " (diffList bL bR)
diffPrimitiveExpression ListBuild ListBuild =
    "…"
diffPrimitiveExpression l@ListBuild r =
    mismatch l r
diffPrimitiveExpression l r@ListBuild =
    mismatch l r
diffPrimitiveExpression ListFold ListFold =
    "…"
diffPrimitiveExpression l@ListFold r =
    mismatch l r
diffPrimitiveExpression l r@ListFold =
    mismatch l r
diffPrimitiveExpression ListLength ListLength =
    "…"
diffPrimitiveExpression l@ListLength r =
    mismatch l r
diffPrimitiveExpression l r@ListLength =
    mismatch l r
diffPrimitiveExpression ListHead ListHead =
    "…"
diffPrimitiveExpression l@ListHead r =
    mismatch l r
diffPrimitiveExpression l r@ListHead =
    mismatch l r
diffPrimitiveExpression ListLast ListLast =
    "…"
diffPrimitiveExpression l@ListLast r =
    mismatch l r
diffPrimitiveExpression l r@ListLast =
    mismatch l r
diffPrimitiveExpression ListIndexed ListIndexed =
    "…"
diffPrimitiveExpression l@ListIndexed r =
    mismatch l r
diffPrimitiveExpression l r@ListIndexed =
    mismatch l r
diffPrimitiveExpression ListReverse ListReverse =
    "…"
diffPrimitiveExpression l@ListReverse r =
    mismatch l r
diffPrimitiveExpression l r@ListReverse =
    mismatch l r
diffPrimitiveExpression Optional Optional =
    "…"
diffPrimitiveExpression l@Optional r =
    mismatch l r
diffPrimitiveExpression l r@Optional =
    mismatch l r
diffPrimitiveExpression None None =
    "…"
diffPrimitiveExpression l@None r =
    mismatch l r
diffPrimitiveExpression l r@None =
    mismatch l r
diffPrimitiveExpression (BoolLit aL) (BoolLit aR) =
    diffBool aL aR
diffPrimitiveExpression l@(BoolLit {}) r =
    mismatch l r
diffPrimitiveExpression l r@(BoolLit {}) =
    mismatch l r
diffPrimitiveExpression (IntegerLit aL) (IntegerLit aR) =
    diffInteger aL aR
diffPrimitiveExpression l@(IntegerLit {}) r =
    mismatch l r
diffPrimitiveExpression l r@(IntegerLit {}) =
    mismatch l r
diffPrimitiveExpression (NaturalLit aL) (NaturalLit aR) =
    diffNatural aL aR
diffPrimitiveExpression l@(NaturalLit {}) r =
    mismatch l r
diffPrimitiveExpression l r@(NaturalLit {}) =
    mismatch l r
diffPrimitiveExpression (DoubleLit aL) (DoubleLit aR) =
    diffDouble aL aR
diffPrimitiveExpression l@(DoubleLit {}) r =
    mismatch l r
diffPrimitiveExpression l r@(DoubleLit {}) =
    mismatch l r
diffPrimitiveExpression (TextLit l) (TextLit r) =
    diffChunks l r
diffPrimitiveExpression l@(TextLit {}) r =
    mismatch l r
diffPrimitiveExpression l r@(TextLit {}) =
    mismatch l r
diffPrimitiveExpression (DateLiteral l) (DateLiteral r) =
    diffDateLiteral l r
diffPrimitiveExpression l@(DateLiteral {}) r =
    mismatch l r
diffPrimitiveExpression l r@(DateLiteral {}) =
    mismatch l r
diffPrimitiveExpression (TimeLiteral tL pL) (TimeLiteral tR pR) =
    diffTimeLiteral tL pL tR pR
diffPrimitiveExpression l@(TimeLiteral {}) r =
    mismatch l r
diffPrimitiveExpression l r@(TimeLiteral {}) =
    mismatch l r
diffPrimitiveExpression (TimeZoneLiteral l) (TimeZoneLiteral r) =
    diffTimeZoneLiteral l r
diffPrimitiveExpression l@(TimeZoneLiteral {}) r =
    mismatch l r
diffPrimitiveExpression l r@(TimeZoneLiteral {}) =
    mismatch l r
diffPrimitiveExpression (Record aL) (Record aR) =
    diffRecord aL aR
diffPrimitiveExpression l@(Record {}) r =
    mismatch l r
diffPrimitiveExpression l r@(Record {}) =
    mismatch l r
diffPrimitiveExpression (RecordLit aL) (RecordLit aR) =
    diffRecordLit aL aR
diffPrimitiveExpression l@(RecordLit {}) r =
    mismatch l r
diffPrimitiveExpression l r@(RecordLit {}) =
    mismatch l r
diffPrimitiveExpression (Union aL) (Union aR) =
    diffUnion aL aR
diffPrimitiveExpression l@(Union {}) r =
    mismatch l r
diffPrimitiveExpression l r@(Union {}) =
    mismatch l r
diffPrimitiveExpression aL aR =
    if same doc
    then ignore
    else align ("( " <> doc <> hardline <> ")")
  where
    doc = diff aL aR
