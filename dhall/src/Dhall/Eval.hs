{-# LANGUAGE AllowAmbiguousTypes  #-}
{-# LANGUAGE BangPatterns         #-}
{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE LambdaCase           #-}
{-# LANGUAGE OverloadedStrings    #-}
{-# LANGUAGE PatternSynonyms      #-}
{-# LANGUAGE RankNTypes           #-}
{-# LANGUAGE ScopedTypeVariables  #-}
{-# LANGUAGE StandaloneDeriving   #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ViewPatterns         #-}

{-# OPTIONS_GHC -O #-}

{-| Eval-apply environment machine with conversion checking and quoting to
    normal forms. Fairly similar to GHCI's STG machine algorithmically, but much
    simpler, with no known call optimization or environment trimming.

    Potential optimizations without changing Expr:

    * In conversion checking, get non-shadowing variables not by linear
      Env-walking, but by keeping track of Env size, and generating names which
      are known to be illegal as source-level names (to rule out shadowing).

    * Use HashMap Text chunks for large let-definitions blocks. "Large" vs
      "Small" is fairly cheap to determine at evaluation time.

    Potential optimizations with changing Expr:

    * Use actual full de Bruijn indices in Var instead of Text counting indices.
      Then, we'd switch to full de Bruijn levels in Val as well, and use proper
      constant time non-shadowing name generation.
-}

module Dhall.Eval (
    judgmentallyEqual
  , normalize
  , alphaNormalize
  , eval
  , quote
  , envNames
  , countNames
  , conv
  , toVHPi
  , Closure(..)
  , Names(..)
  , Environment(..)
  , Val(..)
  , (~>)
  , textShow
  ) where

import Data.Bifunctor     (first)
import Data.Foldable      (foldr', toList)
import Data.List.NonEmpty (NonEmpty(..))
import Data.Sequence      (Seq, ViewL (..), ViewR (..))
import Data.Text          (Text)
import Data.Void          (Void)
import Dhall.Map          (Map)
import Dhall.Set          (Set)
import GHC.Natural        (Natural)
import Prelude            hiding (succ)

import Dhall.Syntax
    ( Binding (..)
    , Chunks (..)
    , Const (..)
    , DhallDouble (..)
    , Expr (..)
    , FunctionBinding (..)
    , PreferAnnotation (..)
    , RecordField (..)
    , Var (..)
    )

import qualified Data.Char
import qualified Data.Sequence as Sequence
import qualified Data.Set
import qualified Data.Text     as Text
import qualified Data.Time     as Time
import qualified Dhall.Map     as Map
import qualified Dhall.Set
import qualified Dhall.Syntax  as Syntax
import qualified Text.Printf

data Environment a
    = Empty
    | Skip   !(Environment a) {-# UNPACK #-} !Text
    | Extend !(Environment a) {-# UNPACK #-} !Text (Val a)

deriving instance (Show a, Show (Val a -> Val a)) => Show (Environment a)

errorMsg :: String
errorMsg = unlines
  [ _ERROR <> ": Compiler bug                                                        "
  , "                                                                                "
  , "An ill-typed expression was encountered during normalization.                   "
  , "Explanation: This error message means that there is a bug in the Dhall compiler."
  , "You didn't do anything wrong, but if you would like to see this problem fixed   "
  , "then you should report the bug at:                                              "
  , "                                                                                "
  , "https://github.com/dhall-lang/dhall-haskell/issues                              "
  ]
  where
    _ERROR :: String
    _ERROR = "\ESC[1;31mError\ESC[0m"


data Closure a = Closure !Text !(Environment a) !(Expr Void a)

deriving instance (Show a, Show (Val a -> Val a)) => Show (Closure a)

data VChunks a = VChunks ![(Text, Val a)] !Text

deriving instance (Show a, Show (Val a -> Val a)) => Show (VChunks a)

instance Semigroup (VChunks a) where
  VChunks xys z <> VChunks [] z' = VChunks xys (z <> z')
  VChunks xys z <> VChunks ((x', y'):xys') z' = VChunks (xys ++ (z <> x', y'):xys') z'

instance Monoid (VChunks a) where
  mempty = VChunks [] mempty

{-| Some information is lost when `eval` converts a `Lam` or a built-in function
    from the `Expr` type to a `VHLam` of the `Val` type and `quote` needs that
    information in order to reconstruct an equivalent `Expr`.  This `HLamInfo`
    type holds that extra information necessary to perform that reconstruction
-}
data HLamInfo a
  = Prim
  -- ^ Don't store any information
  | Typed !Text (Val a)
  -- ^ Store the original name and type of the variable bound by the `Lam`
  | NaturalSubtractZero
  -- ^ The original function was a @Natural/subtract 0@.  We need to preserve
  --   this information in case the @Natural/subtract@ ends up not being fully
  --   saturated, in which case we need to recover the unsaturated built-in
  | TextReplaceEmpty
  -- ^ The original function was a @Text/replace ""@
  | TextReplaceEmptyArgument (Val a)
  -- ^ The original function was a @Text/replace "" replacement@

deriving instance (Show a, Show (Val a -> Val a)) => Show (HLamInfo a)

pattern VPrim :: (Val a -> Val a) -> Val a
pattern VPrim f = VHLam Prim f

toVHPi :: Eq a => Val a -> Maybe (Text, Val a, Val a -> Val a)
toVHPi (VPi a b@(Closure x _ _)) = Just (x, a, instantiate b)
toVHPi (VHPi x a b             ) = Just (x, a, b)
toVHPi  _                        = Nothing
{-# INLINABLE toVHPi #-}

data Val a
    = VConst !Const
    | VVar !Text !Int
    | VPrimVar
    | VApp !(Val a) !(Val a)

    | VLam (Val a) {-# UNPACK #-} !(Closure a)
    | VHLam !(HLamInfo a) !(Val a -> Val a)

    | VPi (Val a) {-# UNPACK #-} !(Closure a)
    | VHPi !Text (Val a) !(Val a -> Val a)

    | VBool
    | VBoolLit !Bool
    | VBoolAnd !(Val a) !(Val a)
    | VBoolOr !(Val a) !(Val a)
    | VBoolEQ !(Val a) !(Val a)
    | VBoolNE !(Val a) !(Val a)
    | VBoolIf !(Val a) !(Val a) !(Val a)

    | VNatural
    | VNaturalLit !Natural
    | VNaturalFold !(Val a) !(Val a) !(Val a) !(Val a)
    | VNaturalBuild !(Val a)
    | VNaturalIsZero !(Val a)
    | VNaturalEven !(Val a)
    | VNaturalOdd !(Val a)
    | VNaturalToInteger !(Val a)
    | VNaturalShow !(Val a)
    | VNaturalSubtract !(Val a) !(Val a)
    | VNaturalPlus !(Val a) !(Val a)
    | VNaturalTimes !(Val a) !(Val a)

    | VInteger
    | VIntegerLit !Integer
    | VIntegerClamp !(Val a)
    | VIntegerNegate !(Val a)
    | VIntegerShow !(Val a)
    | VIntegerToDouble !(Val a)

    | VDouble
    | VDoubleLit !DhallDouble
    | VDoubleShow !(Val a)

    | VText
    | VTextLit !(VChunks a)
    | VTextAppend !(Val a) !(Val a)
    | VTextShow !(Val a)
    | VTextReplace !(Val a) !(Val a) !(Val a)

    | VDate
    | VDateLiteral Time.Day
    | VTime
    | VTimeLiteral Time.TimeOfDay Word
    | VTimeZone
    | VTimeZoneLiteral Time.TimeZone

    | VList !(Val a)
    | VListLit !(Maybe (Val a)) !(Seq (Val a))
    | VListAppend !(Val a) !(Val a)
    | VListBuild   (Val a) !(Val a)
    | VListFold    (Val a) !(Val a) !(Val a) !(Val a) !(Val a)
    | VListLength  (Val a) !(Val a)
    | VListHead    (Val a) !(Val a)
    | VListLast    (Val a) !(Val a)
    | VListIndexed (Val a) !(Val a)
    | VListReverse (Val a) !(Val a)

    | VOptional (Val a)
    | VSome (Val a)
    | VNone (Val a)
    | VRecord !(Map Text (Val a))
    | VRecordLit !(Map Text (Val a))
    | VUnion !(Map Text (Maybe (Val a)))
    | VCombine !(Maybe Text) !(Val a) !(Val a)
    | VCombineTypes !(Val a) !(Val a)
    | VPrefer !(Val a) !(Val a)
    | VMerge !(Val a) !(Val a) !(Maybe (Val a))
    | VToMap !(Val a) !(Maybe (Val a))
    | VField !(Val a) !Text
    | VInject !(Map Text (Maybe (Val a))) !Text !(Maybe (Val a))
    | VProject !(Val a) !(Either (Set Text) (Val a))
    | VAssert !(Val a)
    | VEquivalent !(Val a) !(Val a)
    | VWith !(Val a) (NonEmpty Text) !(Val a)
    | VEmbed a

-- | For use with "Text.Show.Functions".
deriving instance (Show a, Show (Val a -> Val a)) => Show (Val a)

(~>) :: Val a -> Val a -> Val a
(~>) a b = VHPi "_" a (\_ -> b)
{-# INLINE (~>) #-}

infixr 5 ~>

countEnvironment :: Text -> Environment a -> Int
countEnvironment x = go (0 :: Int)
  where
    go !acc Empty             = acc
    go  acc (Skip env x'    ) = go (if x == x' then acc + 1 else acc) env
    go  acc (Extend env x' _) = go (if x == x' then acc + 1 else acc) env

instantiate :: Eq a => Closure a -> Val a -> Val a
instantiate (Closure x env t) !u = eval (Extend env x u) t
{-# INLINE instantiate #-}

-- Out-of-env variables have negative de Bruijn levels.
vVar :: Environment a -> Var -> Val a
vVar env0 (V x i0) = go env0 i0
  where
    go (Extend env x' v) i
        | x == x' =
            if i == 0 then v else go env (i - 1)
        | otherwise =
            go env i
    go (Skip env x') i
        | x == x' =
            if i == 0 then VVar x (countEnvironment x env) else go env (i - 1)
        | otherwise =
            go env i
    go Empty i =
        VVar x (negate i - 1)

vApp :: Eq a => Val a -> Val a -> Val a
vApp !t !u =
    case t of
        VLam _ t'  -> instantiate t' u
        VHLam _ t' -> t' u
        t'        -> VApp t' u
{-# INLINE vApp #-}

vPrefer :: Eq a => Environment a -> Val a -> Val a -> Val a
vPrefer env t u =
    case (t, u) of
        (VRecordLit m, u') | null m ->
            u'
        (t', VRecordLit m) | null m ->
            t'
        (VRecordLit m, VRecordLit m') ->
            VRecordLit (Map.union m' m)
        (t', u') | conv env t' u' ->
            t'
        (t', u') ->
            VPrefer t' u'
{-# INLINE vPrefer #-}

vCombine :: Maybe Text -> Val a -> Val a -> Val a
vCombine mk t u =
    case (t, u) of
        (VRecordLit m, u') | null m ->
            u'
        (t', VRecordLit m) | null m ->
            t'
        (VRecordLit m, VRecordLit m') ->
            VRecordLit (Map.unionWith (vCombine Nothing) m m')
        (t', u') ->
            VCombine mk t' u'

vCombineTypes :: Val a -> Val a -> Val a
vCombineTypes t u =
    case (t, u) of
        (VRecord m, u') | null m ->
            u'
        (t', VRecord m) | null m ->
            t'
        (VRecord m, VRecord m') ->
            VRecord (Map.unionWith vCombineTypes m m')
        (t', u') ->
            VCombineTypes t' u'

vListAppend :: Val a -> Val a -> Val a
vListAppend t u =
    case (t, u) of
        (VListLit _ xs, u') | null xs ->
            u'
        (t', VListLit _ ys) | null ys ->
            t'
        (VListLit t' xs, VListLit _ ys) ->
            VListLit t' (xs <> ys)
        (t', u') ->
            VListAppend t' u'
{-# INLINE vListAppend #-}

vNaturalPlus :: Val a -> Val a -> Val a
vNaturalPlus t u =
    case (t, u) of
        (VNaturalLit 0, u') ->
            u'
        (t', VNaturalLit 0) ->
            t'
        (VNaturalLit m, VNaturalLit n) ->
            VNaturalLit (m + n)
        (t', u') ->
            VNaturalPlus t' u'
{-# INLINE vNaturalPlus #-}

vField :: Val a -> Text -> Val a
vField t0 k = go t0
  where
    go = \case
        VUnion m -> case Map.lookup k m of
            Just (Just _) -> VPrim $ \ ~u -> VInject m k (Just u)
            Just Nothing  -> VInject m k Nothing
            _             -> error errorMsg
        VRecordLit m
            | Just v <- Map.lookup k m -> v
            | otherwise -> error errorMsg
        VProject t _ -> go t
        VPrefer (VRecordLit m) r -> case Map.lookup k m of
            Just v -> VField (VPrefer (singletonVRecordLit v) r) k
            Nothing -> go r
        VPrefer l (VRecordLit m) -> case Map.lookup k m of
            Just v -> v
            Nothing -> go l
        VCombine mk (VRecordLit m) r -> case Map.lookup k m of
            Just v -> VField (VCombine mk (singletonVRecordLit v) r) k
            Nothing -> go r
        VCombine mk l (VRecordLit m) -> case Map.lookup k m of
            Just v -> VField (VCombine mk l (singletonVRecordLit v)) k
            Nothing -> go l
        t -> VField t k

    singletonVRecordLit v = VRecordLit (Map.singleton k v)
{-# INLINE vField #-}

vTextReplace :: Text -> Val a -> Text -> VChunks a
vTextReplace needle replacement haystack = go haystack
  where
    go t
        | Text.null suffix = VChunks [] t
        | otherwise =
            let remainder = Text.drop (Text.length needle) suffix

                rest = go remainder

            in  case replacement of
                    VTextLit replacementChunks ->
                        VChunks [] prefix <> replacementChunks <> rest
                    _ ->
                        VChunks [(prefix, replacement)] "" <> rest
      where
        (prefix, suffix) = Text.breakOn needle t

vProjectByFields :: Eq a => Environment a -> Val a -> Set Text -> Val a
vProjectByFields env t ks =
    if null ks
        then VRecordLit mempty
        else case t of
            VRecordLit kvs ->
                let kvs' = Map.restrictKeys kvs (Dhall.Set.toSet ks)
                in  VRecordLit kvs'
            VProject t' _ ->
                vProjectByFields env t' ks
            VPrefer l (VRecordLit kvs) ->
                let ksSet = Dhall.Set.toSet ks

                    kvs' = Map.restrictKeys kvs ksSet

                    ks' =
                        Dhall.Set.fromSet
                            (Data.Set.difference ksSet (Map.keysSet kvs'))

                in  vPrefer env (vProjectByFields env l ks') (VRecordLit kvs')
            t' ->
                VProject t' (Left ks)

vWith :: Val a -> NonEmpty Text -> Val a -> Val a
vWith (VRecordLit kvs) (k  :| []     ) v = VRecordLit (Map.insert k  v  kvs)
vWith (VRecordLit kvs) (k₀ :| k₁ : ks) v = VRecordLit (Map.insert k₀ e₂ kvs)
  where
    e₁ =
        case Map.lookup k₀ kvs of
            Nothing  -> VRecordLit mempty
            Just e₁' -> e₁'

    e₂ = vWith e₁ (k₁ :| ks) v
vWith e₀ ks v₀ = VWith e₀ ks v₀

eval :: forall a. Eq a => Environment a -> Expr Void a -> Val a
eval !env t0 =
    case t0 of
        Const k ->
            VConst k
        Var v ->
            vVar env v
        Lam _ (FunctionBinding { functionBindingVariable = x, functionBindingAnnotation = a }) t ->
            VLam (eval env a) (Closure x env t)
        Pi _ x a b ->
            VPi (eval env a) (Closure x env b)
        App t u ->
            vApp (eval env t) (eval env u)
        Let (Binding _ x _ _mA _ a) b ->
            let !env' = Extend env x (eval env a)
            in  eval env' b
        Annot t _ ->
            eval env t
        Bool ->
            VBool
        BoolLit b ->
            VBoolLit b
        BoolAnd t u ->
            case (eval env t, eval env u) of
                (VBoolLit True, u')       -> u'
                (VBoolLit False, _)       -> VBoolLit False
                (t', VBoolLit True)       -> t'
                (_ , VBoolLit False)      -> VBoolLit False
                (t', u') | conv env t' u' -> t'
                (t', u')                  -> VBoolAnd t' u'
        BoolOr t u ->
            case (eval env t, eval env u) of
                (VBoolLit False, u')      -> u'
                (VBoolLit True, _)        -> VBoolLit True
                (t', VBoolLit False)      -> t'
                (_ , VBoolLit True)       -> VBoolLit True
                (t', u') | conv env t' u' -> t'
                (t', u')                  -> VBoolOr t' u'
        BoolEQ t u ->
            case (eval env t, eval env u) of
                (VBoolLit True, u')       -> u'
                (t', VBoolLit True)       -> t'
                (t', u') | conv env t' u' -> VBoolLit True
                (t', u')                  -> VBoolEQ t' u'
        BoolNE t u ->
            case (eval env t, eval env u) of
                (VBoolLit False, u')      -> u'
                (t', VBoolLit False)      -> t'
                (t', u') | conv env t' u' -> VBoolLit False
                (t', u')                  -> VBoolNE t' u'
        BoolIf b t f ->
            case (eval env b, eval env t, eval env f) of
                (VBoolLit True,  t', _ )            -> t'
                (VBoolLit False, _ , f')            -> f'
                (b', VBoolLit True, VBoolLit False) -> b'
                (_, t', f') | conv env t' f'        -> t'
                (b', t', f')                        -> VBoolIf b' t' f'
        Natural ->
            VNatural
        NaturalLit n ->
            VNaturalLit n
        NaturalFold ->
            VPrim $ \n ->
            VPrim $ \natural ->
            VPrim $ \succ ->
            VPrim $ \zero ->
            let inert = VNaturalFold n natural succ zero
            in  case zero of
                VPrimVar -> inert
                _ -> case succ of
                    VPrimVar -> inert
                    _ -> case natural of
                        VPrimVar -> inert
                        _ -> case n of
                            VNaturalLit n' ->
                                -- Use an `Integer` for the loop, due to the
                                -- following issue:
                                --
                                -- https://github.com/ghcjs/ghcjs/issues/782
                                let go !acc 0 = acc
                                    go  acc m = go (vApp succ acc) (m - 1)
                                in  go zero (fromIntegral n' :: Integer)
                            _ -> inert
        NaturalBuild ->
            VPrim $ \case
                VPrimVar ->
                    VNaturalBuild VPrimVar
                t ->       t
                    `vApp` VNatural
                    `vApp` VHLam (Typed "n" VNatural) (\n -> vNaturalPlus n (VNaturalLit 1))
                    `vApp` VNaturalLit 0

        NaturalIsZero -> VPrim $ \case
            VNaturalLit n -> VBoolLit (n == 0)
            n             -> VNaturalIsZero n
        NaturalEven -> VPrim $ \case
            VNaturalLit n -> VBoolLit (even n)
            n             -> VNaturalEven n
        NaturalOdd -> VPrim $ \case
            VNaturalLit n -> VBoolLit (odd n)
            n             -> VNaturalOdd n
        NaturalToInteger -> VPrim $ \case
            VNaturalLit n -> VIntegerLit (fromIntegral n)
            n             -> VNaturalToInteger n
        NaturalShow -> VPrim $ \case
            VNaturalLit n -> VTextLit (VChunks [] (Text.pack (show n)))
            n             -> VNaturalShow n
        NaturalSubtract -> VPrim $ \case
            VNaturalLit 0 ->
                VHLam NaturalSubtractZero id
            x@(VNaturalLit m) ->
                VPrim $ \case
                    VNaturalLit n
                        | n >= m ->
                            -- Use an `Integer` for the subtraction, due to the
                            -- following issue:
                            --
                            -- https://github.com/ghcjs/ghcjs/issues/782
                            VNaturalLit (fromIntegral (subtract (fromIntegral m :: Integer) (fromIntegral n :: Integer)))
                        | otherwise -> VNaturalLit 0
                    y -> VNaturalSubtract x y
            x ->
                VPrim $ \case
                    VNaturalLit 0    -> VNaturalLit 0
                    y | conv env x y -> VNaturalLit 0
                    y                -> VNaturalSubtract x y
        NaturalPlus t u ->
            vNaturalPlus (eval env t) (eval env u)
        NaturalTimes t u ->
            case (eval env t, eval env u) of
                (VNaturalLit 1, u'           ) -> u'
                (t'           , VNaturalLit 1) -> t'
                (VNaturalLit 0, _            ) -> VNaturalLit 0
                (_            , VNaturalLit 0) -> VNaturalLit 0
                (VNaturalLit m, VNaturalLit n) -> VNaturalLit (m * n)
                (t'           , u'           ) -> VNaturalTimes t' u'
        Integer ->
            VInteger
        IntegerLit n ->
            VIntegerLit n
        IntegerClamp ->
            VPrim $ \case
                VIntegerLit n
                    | 0 <= n    -> VNaturalLit (fromInteger n)
                    | otherwise -> VNaturalLit 0
                n -> VIntegerClamp n
        IntegerNegate ->
            VPrim $ \case
                VIntegerLit n -> VIntegerLit (negate n)
                n             -> VIntegerNegate n
        IntegerShow ->
            VPrim $ \case
                VIntegerLit n
                    | 0 <= n    -> VTextLit (VChunks [] (Text.pack ('+':show n)))
                    | otherwise -> VTextLit (VChunks [] (Text.pack (show n)))
                n -> VIntegerShow n
        IntegerToDouble ->
            VPrim $ \case
                VIntegerLit n -> VDoubleLit (DhallDouble (read (show n)))
                -- `(read . show)` is used instead of `fromInteger`
                -- because `read` uses the correct rounding rule.
                -- See https://gitlab.haskell.org/ghc/ghc/issues/17231.
                n             -> VIntegerToDouble n
        Double ->
            VDouble
        DoubleLit n ->
            VDoubleLit n
        DoubleShow ->
            VPrim $ \case
                VDoubleLit (DhallDouble n) -> VTextLit (VChunks [] (Text.pack (show n)))
                n                          -> VDoubleShow n
        Text ->
            VText
        TextLit cs ->
            case evalChunks cs of
                VChunks [("", t)] "" -> t
                vcs                  -> VTextLit vcs
        TextAppend t u ->
            eval env (TextLit (Chunks [("", t), ("", u)] ""))
        TextShow ->
            VPrim $ \case
                VTextLit (VChunks [] x) -> VTextLit (VChunks [] (textShow x))
                t                       -> VTextShow t
        TextReplace ->
            VPrim $ \needle ->
            let hLamInfo0 = case needle of
                    VTextLit (VChunks [] "") -> TextReplaceEmpty
                    _                        -> Prim

            in  VHLam hLamInfo0 $ \replacement ->
            let hLamInfo1 = case needle of
                    VTextLit (VChunks [] "") ->
                        TextReplaceEmptyArgument replacement
                    _ ->
                        Prim
            in  VHLam hLamInfo1 $ \haystack ->
                    case needle of
                        VTextLit (VChunks [] "") ->
                            haystack

                        VTextLit (VChunks [] needleText) ->
                            case haystack of
                                VTextLit (VChunks [] haystackText) ->
                                    case replacement of
                                        VTextLit (VChunks [] replacementText) ->
                                            VTextLit $ VChunks []
                                                (Text.replace
                                                    needleText
                                                    replacementText
                                                    haystackText
                                                )
                                        _ ->
                                            VTextLit
                                                (vTextReplace
                                                    needleText
                                                    replacement
                                                    haystackText
                                                )
                                _ ->
                                    VTextReplace needle replacement haystack
                        _ ->
                            VTextReplace needle replacement haystack
        Date ->
            VDate
        DateLiteral d ->
            VDateLiteral d
        Time ->
            VTime
        TimeLiteral t p ->
            VTimeLiteral t p
        TimeZone ->
            VTimeZone
        TimeZoneLiteral z ->
            VTimeZoneLiteral z
        List ->
            VPrim VList
        ListLit ma ts ->
            VListLit (fmap (eval env) ma) (fmap (eval env) ts)
        ListAppend t u ->
            vListAppend (eval env t) (eval env u)
        ListBuild ->
            VPrim $ \a ->
            VPrim $ \case
                VPrimVar ->
                    VListBuild a VPrimVar
                t ->       t
                    `vApp` VList a
                    `vApp` VHLam (Typed "a" a) (\x ->
                           VHLam (Typed "as" (VList a)) (\as ->
                           vListAppend (VListLit Nothing (pure x)) as))
                    `vApp` VListLit (Just (VList a)) mempty

        ListFold ->
            VPrim $ \a ->
            VPrim $ \as ->
            VPrim $ \list ->
            VPrim $ \cons ->
            VPrim $ \nil ->
            let inert = VListFold a as list cons nil
            in  case nil of
                VPrimVar -> inert
                _ -> case cons of
                    VPrimVar -> inert
                    _ -> case list of
                        VPrimVar -> inert
                        _ -> case a of
                            VPrimVar -> inert
                            _ -> case as of
                                VListLit _ as' ->
                                    foldr' (\x b -> cons `vApp` x `vApp` b) nil as'
                                _ -> inert
        ListLength ->
            VPrim $ \ a ->
            VPrim $ \case
                VListLit _ as -> VNaturalLit (fromIntegral (Sequence.length as))
                as            -> VListLength a as
        ListHead ->
            VPrim $ \ a ->
            VPrim $ \case
                VListLit _ as ->
                    case Sequence.viewl as of
                        y :< _ -> VSome y
                        _      -> VNone a
                as ->
                    VListHead a as
        ListLast ->
            VPrim $ \ a ->
            VPrim $ \case
                VListLit _ as ->
                    case Sequence.viewr as of
                        _ :> t -> VSome t
                        _      -> VNone a
                as -> VListLast a as
        ListIndexed ->
            VPrim $ \ a ->
            VPrim $ \case
                VListLit _ as ->
                    let a' =
                            if null as
                            then Just (VList (VRecord (Map.unorderedFromList [("index", VNatural), ("value", a)])))
                            else Nothing

                        as' =
                            Sequence.mapWithIndex
                                (\i t ->
                                    VRecordLit
                                        (Map.unorderedFromList
                                            [ ("index", VNaturalLit (fromIntegral i))
                                            , ("value", t)
                                            ]
                                        )
                                )
                                as

                        in  VListLit a' as'
                t ->
                    VListIndexed a t
        ListReverse ->
            VPrim $ \ ~a ->
            VPrim $ \case
                VListLit t as | null as ->
                    VListLit t as
                VListLit _ as ->
                    VListLit Nothing (Sequence.reverse as)
                t ->
                    VListReverse a t
        Optional ->
            VPrim VOptional
        Some t ->
            VSome (eval env t)
        None ->
            VPrim $ \ ~a -> VNone a
        Record kts ->
            VRecord (Map.sort (eval env . recordFieldValue <$> kts))
        RecordLit kts ->
            VRecordLit (Map.sort (eval env . recordFieldValue <$> kts))
        Union kts ->
            VUnion (Map.sort (fmap (fmap (eval env)) kts))
        Combine _ mk t u ->
            vCombine mk (eval env t) (eval env u)
        CombineTypes _ t u ->
            vCombineTypes (eval env t) (eval env u)
        Prefer _ _ t u ->
            vPrefer env (eval env t) (eval env u)
        RecordCompletion t u ->
            eval env (Annot (Prefer mempty PreferFromCompletion (Field t def) u) (Field t typ))
          where
            def = Syntax.makeFieldSelection "default"
            typ = Syntax.makeFieldSelection "Type"
        Merge x y ma ->
            case (eval env x, eval env y, fmap (eval env) ma) of
                (VRecordLit m, VInject _ k mt, _)
                    | Just f <- Map.lookup k m -> maybe f (vApp f) mt
                    | otherwise                -> error errorMsg
                (VRecordLit m, VSome t, _)
                    | Just f <- Map.lookup "Some" m -> vApp f t
                    | otherwise                     -> error errorMsg
                (VRecordLit m, VNone _, _)
                    | Just t <- Map.lookup "None" m -> t
                    | otherwise                     -> error errorMsg
                (x', y', ma') -> VMerge x' y' ma'
        ToMap x ma ->
            case (eval env x, fmap (eval env) ma) of
                (VRecordLit m, ma'@(Just _)) | null m ->
                    VListLit ma' Sequence.empty
                (VRecordLit m, _) ->
                    let entry (k, v) =
                            VRecordLit
                                (Map.unorderedFromList
                                    [ ("mapKey", VTextLit $ VChunks [] k)
                                    , ("mapValue", v)
                                    ]
                                )

                        s = (Sequence.fromList . map entry . Map.toAscList) m

                    in  VListLit Nothing s
                (x', ma') ->
                    VToMap x' ma'
        Field t (Syntax.fieldSelectionLabel -> k) ->
            vField (eval env t) k
        Project t (Left ks) ->
            vProjectByFields env (eval env t) (Dhall.Set.sort (Dhall.Set.fromList ks))
        Project t (Right e) ->
            case eval env e of
                VRecord kts ->
                    vProjectByFields env (eval env t) (Dhall.Set.fromSet (Map.keysSet kts))
                e' ->
                    VProject (eval env t) (Right e')
        Assert t ->
            VAssert (eval env t)
        Equivalent _ t u ->
            VEquivalent (eval env t) (eval env u)
        With e₀ ks v ->
            vWith (eval env e₀) ks (eval env v)
        Note _ e ->
            eval env e
        ImportAlt t _ ->
            eval env t
        Embed a ->
            VEmbed a
  where
    evalChunks :: Chunks Void a -> VChunks a
    evalChunks (Chunks xys z) = foldr' cons nil xys
      where
        cons (x, t) vcs =
            case eval env t of
                VTextLit vcs' -> VChunks [] x <> vcs' <> vcs
                t'            -> VChunks [(x, t')] mempty <> vcs

        nil = VChunks [] z
    {-# INLINE evalChunks #-}

eqListBy :: (a -> a -> Bool) -> [a] -> [a] -> Bool
eqListBy f = go
  where
    go (x:xs) (y:ys) | f x y = go xs ys
    go [] [] = True
    go _  _  = False
{-# INLINE eqListBy #-}

eqMapsBy :: Ord k => (v -> v -> Bool) -> Map k v -> Map k v -> Bool
eqMapsBy f mL mR =
    Map.size mL == Map.size mR
    && eqListBy eq (Map.toAscList mL) (Map.toAscList mR)
  where
    eq (kL, vL) (kR, vR) = kL == kR && f vL vR
{-# INLINE eqMapsBy #-}

eqMaybeBy :: (a -> a -> Bool) -> Maybe a -> Maybe a -> Bool
eqMaybeBy f = go
  where
    go (Just x) (Just y) = f x y
    go Nothing  Nothing  = True
    go _        _        = False
{-# INLINE eqMaybeBy #-}

-- | Utility that powers the @Text/show@ built-in
textShow :: Text -> Text
textShow text = "\"" <> Text.concatMap f text <> "\""
  where
    f '"'  = "\\\""
    f '$'  = "\\u0024"
    f '\\' = "\\\\"
    f '\b' = "\\b"
    f '\n' = "\\n"
    f '\r' = "\\r"
    f '\t' = "\\t"
    f '\f' = "\\f"
    f c | c <= '\x1F' = Text.pack (Text.Printf.printf "\\u%04x" (Data.Char.ord c))
        | otherwise   = Text.singleton c

conv :: forall a. Eq a => Environment a -> Val a -> Val a -> Bool
conv !env t0 t0' =
    case (t0, t0') of
        (VConst k, VConst k') ->
            k == k'
        (VVar x i, VVar x' i') ->
            x == x' && i == i'
        (VLam _ (freshClosure -> (x, v, t)), VLam _ t' ) ->
            convSkip x (instantiate t v) (instantiate t' v)
        (VLam _ (freshClosure -> (x, v, t)), VHLam _ t') ->
            convSkip x (instantiate t v) (t' v)
        (VLam _ (freshClosure -> (x, v, t)), t'        ) ->
            convSkip x (instantiate t v) (vApp t' v)
        (VHLam _ t, VLam _ (freshClosure -> (x, v, t'))) ->
            convSkip x (t v) (instantiate t' v)
        (VHLam _ t, VHLam _ t'                    ) ->
            let (x, v) = fresh "x" in convSkip x (t v) (t' v)
        (VHLam _ t, t'                            ) ->
            let (x, v) = fresh "x" in convSkip x (t v) (vApp t' v)
        (t, VLam _ (freshClosure -> (x, v, t'))) ->
            convSkip x (vApp t v) (instantiate t' v)
        (t, VHLam _ t'  ) ->
            let (x, v) = fresh "x" in convSkip x (vApp t v) (t' v)
        (VApp t u, VApp t' u') ->
            conv env t t' && conv env u u'
        (VPi a b, VPi a' (freshClosure -> (x, v, b'))) ->
            conv env a a' && convSkip x (instantiate b v) (instantiate b' v)
        (VPi a b, VHPi (fresh -> (x, v)) a' b') ->
            conv env a a' && convSkip x (instantiate b v) (b' v)
        (VHPi _ a b, VPi a' (freshClosure -> (x, v, b'))) ->
            conv env a a' && convSkip x (b v) (instantiate b' v)
        (VHPi _ a b, VHPi (fresh -> (x, v)) a' b') ->
            conv env a a' && convSkip x (b v) (b' v)
        (VBool, VBool) ->
            True
        (VBoolLit b, VBoolLit b') ->
            b == b'
        (VBoolAnd t u, VBoolAnd t' u') ->
            conv env t t' && conv env u u'
        (VBoolOr t u, VBoolOr t' u') ->
            conv env t t' && conv env u u'
        (VBoolEQ t u, VBoolEQ t' u') ->
            conv env t t' && conv env u u'
        (VBoolNE t u, VBoolNE t' u') ->
            conv env t t' && conv env u u'
        (VBoolIf t u v, VBoolIf t' u' v') ->
            conv env t t' && conv env u u' && conv env v v'
        (VNatural, VNatural) ->
            True
        (VNaturalLit n, VNaturalLit n') ->
            n == n'
        (VNaturalFold t _ u v, VNaturalFold t' _ u' v') ->
            conv env t t' && conv env u u' && conv env v v'
        (VNaturalBuild t, VNaturalBuild t') ->
            conv env t t'
        (VNaturalIsZero t, VNaturalIsZero t') ->
            conv env t t'
        (VNaturalEven t, VNaturalEven t') ->
            conv env t t'
        (VNaturalOdd t, VNaturalOdd t') ->
            conv env t t'
        (VNaturalToInteger t, VNaturalToInteger t') ->
            conv env t t'
        (VNaturalShow t, VNaturalShow t') ->
            conv env t t'
        (VNaturalSubtract x y, VNaturalSubtract x' y') ->
            conv env x x' && conv env y y'
        (VNaturalPlus t u, VNaturalPlus t' u') ->
            conv env t t' && conv env u u'
        (VNaturalTimes t u, VNaturalTimes t' u') ->
            conv env t t' && conv env u u'
        (VInteger, VInteger) ->
            True
        (VIntegerLit t, VIntegerLit t') ->
            t == t'
        (VIntegerClamp t, VIntegerClamp t') ->
            conv env t t'
        (VIntegerNegate t, VIntegerNegate t') ->
            conv env t t'
        (VIntegerShow t, VIntegerShow t') ->
            conv env t t'
        (VIntegerToDouble t, VIntegerToDouble t') ->
            conv env t t'
        (VDouble, VDouble) ->
            True
        (VDoubleLit n, VDoubleLit n') ->
            n == n'
        (VDoubleShow t, VDoubleShow t') ->
            conv env t t'
        (VText, VText) ->
            True
        (VTextLit cs, VTextLit cs') ->
            convChunks cs cs'
        (VTextAppend t u, VTextAppend t' u') ->
            conv env t t' && conv env u u'
        (VTextShow t, VTextShow t') ->
            conv env t t'
        (VTextReplace a b c, VTextReplace a' b' c') ->
            conv env a a' && conv env b b' && conv env c c'
        (VList a, VList a') ->
            conv env a a'
        (VListLit _ xs, VListLit _ xs') ->
            eqListBy (conv env) (toList xs) (toList xs')
        (VListAppend t u, VListAppend t' u') ->
            conv env t t' && conv env u u'
        (VListBuild _ t, VListBuild _ t') ->
            conv env t t'
        (VListLength a t, VListLength a' t') ->
            conv env a a' && conv env t t'
        (VListHead _ t, VListHead _ t') ->
            conv env t t'
        (VListLast _ t, VListLast _ t') ->
            conv env t t'
        (VListIndexed _ t, VListIndexed _ t') ->
            conv env t t'
        (VListReverse _ t, VListReverse _ t') ->
            conv env t t'
        (VListFold a l _ t u, VListFold a' l' _ t' u') ->
            conv env a a' && conv env l l' && conv env t t' && conv env u u'
        (VOptional a, VOptional a') ->
            conv env a a'
        (VSome t, VSome t') ->
            conv env t t'
        (VNone _, VNone _) ->
            True
        (VRecord m, VRecord m') ->
            eqMapsBy (conv env) m m'
        (VRecordLit m, VRecordLit m') ->
            eqMapsBy (conv env) m m'
        (VUnion m, VUnion m') ->
            eqMapsBy (eqMaybeBy (conv env)) m m'
        (VCombine _ t u, VCombine _ t' u') ->
            conv env t t' && conv env u u'
        (VCombineTypes t u, VCombineTypes t' u') ->
            conv env t t' && conv env u u'
        (VPrefer t u, VPrefer t' u') ->
            conv env t t' && conv env u u'
        (VMerge t u _, VMerge t' u' _) ->
            conv env t t' && conv env u u'
        (VToMap t _, VToMap t' _) ->
            conv env t t'
        (VField t k, VField t' k') ->
            conv env t t' && k == k'
        (VProject t (Left ks), VProject t' (Left ks')) ->
            conv env t t' && ks == ks'
        (VProject t (Right e), VProject t' (Right e')) ->
            conv env t t' && conv env e e'
        (VAssert t, VAssert t') ->
            conv env t t'
        (VEquivalent t u, VEquivalent t' u') ->
            conv env t t' && conv env u u'
        (VInject m k mt, VInject m' k' mt') ->
            eqMapsBy (eqMaybeBy (conv env)) m m' && k == k' && eqMaybeBy (conv env) mt mt'
        (VEmbed a, VEmbed a') ->
            a == a'
        (_, _) ->
            False
  where
    fresh :: Text -> (Text, Val a)
    fresh x = (x, VVar x (countEnvironment x env))
    {-# INLINE fresh #-}

    freshClosure :: Closure a -> (Text, Val a, Closure a)
    freshClosure closure@(Closure x _ _) = (x, snd (fresh x), closure)
    {-# INLINE freshClosure #-}

    convChunks :: VChunks a -> VChunks a -> Bool
    convChunks (VChunks xys z) (VChunks xys' z') =
      eqListBy (\(x, y) (x', y') -> x == x' && conv env y y') xys xys' && z == z'
    {-# INLINE convChunks #-}

    convSkip :: Text -> Val a -> Val a -> Bool
    convSkip x = conv (Skip env x)
    {-# INLINE convSkip #-}

judgmentallyEqual :: Eq a => Expr s a -> Expr t a -> Bool
judgmentallyEqual (Syntax.denote -> t) (Syntax.denote -> u) =
    conv Empty (eval Empty t) (eval Empty u)
{-# INLINABLE judgmentallyEqual #-}

data Names
  = EmptyNames
  | Bind !Names {-# UNPACK #-} !Text
  deriving Show

envNames :: Environment a -> Names
envNames Empty = EmptyNames
envNames (Skip   env x  ) = Bind (envNames env) x
envNames (Extend env x _) = Bind (envNames env) x

countNames :: Text -> Names -> Int
countNames x = go 0
  where
    go !acc EmptyNames         = acc
    go  acc (Bind env x') = go (if x == x' then acc + 1 else acc) env

-- | Quote a value into beta-normal form.
quote :: forall a. Eq a => Names -> Val a -> Expr Void a
quote !env !t0 =
    case t0 of
        VConst k ->
            Const k
        VVar !x !i ->
            Var (V x (countNames x env - i - 1))
        VApp t u ->
            quote env t `qApp` u
        VLam a (freshClosure -> (x, v, t)) ->
            Lam
                mempty
                (Syntax.makeFunctionBinding x (quote env a))
                (quoteBind x (instantiate t v))
        VHLam i t ->
            case i of
                Typed (fresh -> (x, v)) a ->
                    Lam mempty
                        (Syntax.makeFunctionBinding x (quote env a))
                        (quoteBind x (t v))
                Prim ->
                    quote env (t VPrimVar)
                NaturalSubtractZero ->
                    App NaturalSubtract (NaturalLit 0)
                TextReplaceEmpty ->
                    App TextReplace (TextLit (Chunks [] ""))
                TextReplaceEmptyArgument replacement ->
                    App (App TextReplace (TextLit (Chunks [] "")))
                        (quote env replacement)

        VPi a (freshClosure -> (x, v, b)) ->
            Pi mempty x (quote env a) (quoteBind x (instantiate b v))
        VHPi (fresh -> (x, v)) a b ->
            Pi mempty x (quote env a) (quoteBind x (b v))
        VBool ->
            Bool
        VBoolLit b ->
            BoolLit b
        VBoolAnd t u ->
            BoolAnd (quote env t) (quote env u)
        VBoolOr t u ->
            BoolOr (quote env t) (quote env u)
        VBoolEQ t u ->
            BoolEQ (quote env t) (quote env u)
        VBoolNE t u ->
            BoolNE (quote env t) (quote env u)
        VBoolIf t u v ->
            BoolIf (quote env t) (quote env u) (quote env v)
        VNatural ->
            Natural
        VNaturalLit n ->
            NaturalLit n
        VNaturalFold a t u v ->
            NaturalFold `qApp` a `qApp` t `qApp` u `qApp` v
        VNaturalBuild t ->
            NaturalBuild `qApp` t
        VNaturalIsZero t ->
            NaturalIsZero `qApp` t
        VNaturalEven t ->
            NaturalEven `qApp` t
        VNaturalOdd t ->
            NaturalOdd `qApp` t
        VNaturalToInteger t ->
            NaturalToInteger `qApp` t
        VNaturalShow t ->
            NaturalShow `qApp` t
        VNaturalPlus t u ->
            NaturalPlus (quote env t) (quote env u)
        VNaturalTimes t u ->
            NaturalTimes (quote env t) (quote env u)
        VNaturalSubtract x y ->
            NaturalSubtract `qApp` x `qApp` y
        VInteger ->
            Integer
        VIntegerLit n ->
            IntegerLit n
        VIntegerClamp t ->
            IntegerClamp `qApp` t
        VIntegerNegate t ->
            IntegerNegate `qApp` t
        VIntegerShow t ->
            IntegerShow `qApp` t
        VIntegerToDouble t ->
            IntegerToDouble `qApp` t
        VDouble ->
            Double
        VDoubleLit n ->
            DoubleLit n
        VDoubleShow t ->
            DoubleShow `qApp` t
        VText ->
            Text
        VTextLit (VChunks xys z) ->
            TextLit (Chunks (fmap (fmap (quote env)) xys) z)
        VTextAppend t u ->
            TextAppend (quote env t) (quote env u)
        VTextShow t ->
            TextShow `qApp` t
        VTextReplace a b c ->
            TextReplace `qApp` a `qApp` b `qApp` c
        VDate ->
            Date
        VDateLiteral d ->
            DateLiteral d
        VTime ->
            Time
        VTimeLiteral t p ->
            TimeLiteral t p
        VTimeZone ->
            TimeZone
        VTimeZoneLiteral z ->
            TimeZoneLiteral z
        VList t ->
            List `qApp` t
        VListLit ma ts ->
            ListLit (fmap (quote env) ma) (fmap (quote env) ts)
        VListAppend t u ->
            ListAppend (quote env t) (quote env u)
        VListBuild a t ->
            ListBuild `qApp` a `qApp` t
        VListFold a l t u v ->
            ListFold `qApp` a `qApp` l `qApp` t `qApp` u `qApp` v
        VListLength a t ->
            ListLength `qApp` a `qApp` t
        VListHead a t ->
            ListHead `qApp` a `qApp` t
        VListLast a t ->
            ListLast `qApp` a `qApp` t
        VListIndexed a t ->
            ListIndexed `qApp` a `qApp` t
        VListReverse a t ->
            ListReverse `qApp` a `qApp` t
        VOptional a ->
            Optional `qApp` a
        VSome t ->
            Some (quote env t)
        VNone t ->
            None `qApp` t
        VRecord m ->
            Record (fmap quoteRecordField m)
        VRecordLit m ->
            RecordLit (fmap quoteRecordField m)
        VUnion m ->
            Union (fmap (fmap (quote env)) m)
        VCombine mk t u ->
            Combine mempty mk (quote env t) (quote env u)
        VCombineTypes t u ->
            CombineTypes mempty (quote env t) (quote env u)
        VPrefer t u ->
            Prefer mempty PreferFromSource (quote env t) (quote env u)
        VMerge t u ma ->
            Merge (quote env t) (quote env u) (fmap (quote env) ma)
        VToMap t ma ->
            ToMap (quote env t) (fmap (quote env) ma)
        VField t k ->
            Field (quote env t) $ Syntax.makeFieldSelection k
        VProject t p ->
            Project (quote env t) (first Dhall.Set.toList (fmap (quote env) p))
        VAssert t ->
            Assert (quote env t)
        VEquivalent t u ->
            Equivalent mempty (quote env t) (quote env u)
        VWith e ks v ->
            With (quote env e) ks (quote env v)
        VInject m k Nothing ->
            Field (Union (fmap (fmap (quote env)) m)) $ Syntax.makeFieldSelection k
        VInject m k (Just t) ->
            Field (Union (fmap (fmap (quote env)) m)) (Syntax.makeFieldSelection k) `qApp` t
        VEmbed a ->
            Embed a
        VPrimVar ->
            error errorMsg
  where
    fresh :: Text -> (Text, Val a)
    fresh x = (x, VVar x (countNames x env))
    {-# INLINE fresh #-}

    freshClosure :: Closure a -> (Text, Val a, Closure a)
    freshClosure closure@(Closure x _ _) = (x, snd (fresh x), closure)
    {-# INLINE freshClosure #-}

    quoteBind :: Text -> Val a -> Expr Void a
    quoteBind x = quote (Bind env x)
    {-# INLINE quoteBind #-}

    qApp :: Expr Void a -> Val a -> Expr Void a
    qApp t VPrimVar = t
    qApp t u        = App t (quote env u)
    {-# INLINE qApp #-}

    quoteRecordField :: Val a -> RecordField Void a
    quoteRecordField = Syntax.makeRecordField . quote env
    {-# INLINE quoteRecordField #-}

-- | Normalize an expression in an environment of values. Any variable pointing out of
--   the environment is treated as opaque free variable.
nf :: Eq a => Environment a -> Expr s a -> Expr t a
nf !env = Syntax.renote . quote (envNames env) . eval env . Syntax.denote

normalize :: Eq a => Expr s a -> Expr t a
normalize = nf Empty
{-# INLINABLE normalize #-}

alphaNormalize :: Expr s a -> Expr s a
alphaNormalize = goEnv EmptyNames
  where
    goVar :: Names -> Text -> Int -> Expr s a
    goVar e topX topI = go 0 e topI
      where
        go !acc (Bind env x) !i
          | x == topX = if i == 0 then Var (V "_" acc) else go (acc + 1) env (i - 1)
          | otherwise = go (acc + 1) env i
        go _ EmptyNames i = Var (V topX i)

    goEnv :: Names -> Expr s a -> Expr s a
    goEnv !e0 t0 =
        case t0 of
            Const k ->
                Const k
            Var (V x i) ->
                goVar e0 x i
            Lam cs (FunctionBinding src0 x src1 src2 t) u ->
                Lam cs (FunctionBinding src0 "_" src1 src2 (go t)) (goBind x u)
            Pi cs x a b ->
                Pi cs "_" (go a) (goBind x b)
            App t u ->
                App (go t) (go u)
            Let (Binding src0 x src1 mA src2 a) b ->
                Let (Binding src0 "_" src1 (fmap (fmap go) mA) src2 (go a)) (goBind x b)
            Annot t u ->
                Annot (go t) (go u)
            Bool ->
                Bool
            BoolLit b ->
                BoolLit b
            BoolAnd t u ->
                BoolAnd (go t) (go u)
            BoolOr t u ->
                BoolOr  (go t) (go u)
            BoolEQ t u ->
                BoolEQ  (go t) (go u)
            BoolNE t u ->
                BoolNE  (go t) (go u)
            BoolIf b t f ->
                BoolIf  (go b) (go t) (go f)
            Natural ->
                Natural
            NaturalLit n ->
                NaturalLit n
            NaturalFold ->
                NaturalFold
            NaturalBuild ->
                NaturalBuild
            NaturalIsZero ->
                NaturalIsZero
            NaturalEven ->
                NaturalEven
            NaturalOdd ->
                NaturalOdd
            NaturalToInteger ->
                NaturalToInteger
            NaturalShow ->
                NaturalShow
            NaturalSubtract ->
                NaturalSubtract
            NaturalPlus t u ->
                NaturalPlus (go t) (go u)
            NaturalTimes t u ->
                NaturalTimes (go t) (go u)
            Integer ->
                Integer
            IntegerLit n ->
                IntegerLit n
            IntegerClamp ->
                IntegerClamp
            IntegerNegate ->
                IntegerNegate
            IntegerShow ->
                IntegerShow
            IntegerToDouble ->
                IntegerToDouble
            Double ->
                Double
            DoubleLit n ->
                DoubleLit n
            DoubleShow ->
                DoubleShow
            Text ->
                Text
            TextLit cs ->
                TextLit (goChunks cs)
            TextAppend t u ->
                TextAppend (go t) (go u)
            TextShow ->
                TextShow
            TextReplace ->
                TextReplace
            Date ->
                Date
            DateLiteral d ->
                DateLiteral d
            Time ->
                Time
            TimeLiteral t p ->
                TimeLiteral t p
            TimeZone ->
                TimeZone
            TimeZoneLiteral z ->
                TimeZoneLiteral z
            List ->
                List
            ListLit ma ts ->
                ListLit (fmap go ma) (fmap go ts)
            ListAppend t u ->
                ListAppend (go t) (go u)
            ListBuild ->
                ListBuild
            ListFold ->
                ListFold
            ListLength ->
                ListLength
            ListHead ->
                ListHead
            ListLast ->
                ListLast
            ListIndexed ->
                ListIndexed
            ListReverse ->
                ListReverse
            Optional ->
                Optional
            Some t ->
                Some (go t)
            None ->
                None
            Record kts ->
                Record (goRecordField <$> kts)
            RecordLit kts ->
                RecordLit (goRecordField <$> kts)
            Union kts ->
                Union (fmap (fmap go) kts)
            Combine cs m t u ->
                Combine cs m (go t) (go u)
            CombineTypes cs t u ->
                CombineTypes cs (go t) (go u)
            Prefer cs b t u ->
                Prefer cs b (go t) (go u)
            RecordCompletion t u ->
                RecordCompletion (go t) (go u)
            Merge x y ma ->
                Merge (go x) (go y) (fmap go ma)
            ToMap x ma ->
                ToMap (go x) (fmap go ma)
            Field t k ->
                Field (go t) k
            Project t ks ->
                Project (go t) (fmap go ks)
            Assert t ->
                Assert (go t)
            Equivalent cs t u ->
                Equivalent cs (go t) (go u)
            With e k v ->
                With (go e) k (go v)
            Note s e ->
                Note s (go e)
            ImportAlt t u ->
                ImportAlt (go t) (go u)
            Embed a ->
                Embed a
      where
        go                     = goEnv e0
        goBind x               = goEnv (Bind e0 x)
        goChunks (Chunks ts x) = Chunks (fmap (fmap go) ts) x
        goRecordField (RecordField s0 e s1 s2) = RecordField s0 (go e) s1 s2
