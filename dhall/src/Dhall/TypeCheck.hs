{-# LANGUAGE DeriveDataTypeable  #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE RecordWildCards     #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ViewPatterns        #-}

{-# OPTIONS_GHC -Wall #-}

-- | This module contains the logic for type checking Dhall code

module Dhall.TypeCheck (
    -- * Type-checking
      typeWith
    , typeOf
    , typeWithA
    , checkContext
    , messageExpressions

    -- * Types
    , Typer
    , X
    , absurd
    , TypeError(..)
    , DetailedTypeError(..)
    , Censored(..)
    , TypeMessage(..)
    , prettyTypeMessage
    , ErrorMessages(..)
    ) where

import Control.Exception                 (Exception)
import Control.Monad.Trans.Class         (lift)
import Control.Monad.Trans.Writer.Strict (execWriterT, tell)
import Data.List.NonEmpty                (NonEmpty (..))
import Data.Monoid                       (Endo (..))
import Data.Semigroup                    (Max (..))
import Data.Sequence                     (Seq, ViewL (..))
import Data.Set                          (Set)
import Data.Text                         (Text)
import Data.Text.Prettyprint.Doc         (Doc, Pretty (..), vsep)
import Data.Typeable                     (Typeable)
import Data.Void                         (Void, absurd)
import Dhall.Context                     (Context)
import Dhall.Eval
    ( Environment (..)
    , Names (..)
    , Val (..)
    , (~>)
    )
import Dhall.Pretty                      (Ann)
import Dhall.Src                         (Src)
import Lens.Family                       (over)

import Dhall.Syntax
    ( Binding (..)
    , Chunks (..)
    , Const (..)
    , Expr (..)
    , FunctionBinding (..)
    , PreferAnnotation (..)
    , RecordField (..)
    , Var (..)
    )

import qualified Data.Foldable                           as Foldable
import qualified Data.List.NonEmpty                      as NonEmpty
import qualified Data.Map
import qualified Data.Sequence
import qualified Data.Set
import qualified Data.Text                               as Text
import qualified Data.Text.Prettyprint.Doc               as Pretty
import qualified Data.Text.Prettyprint.Doc.Render.String as Pretty
import qualified Data.Traversable
import qualified Dhall.Context
import qualified Dhall.Core
import qualified Dhall.Diff
import qualified Dhall.Eval                              as Eval
import qualified Dhall.Map
import qualified Dhall.Pretty
import qualified Dhall.Pretty.Internal
import qualified Dhall.Syntax                            as Syntax
import qualified Dhall.Util
import qualified Lens.Family

{-| A type synonym for `Void`

    This is provided for backwards compatibility, since Dhall used to use its
    own `X` type instead of @"Data.Void".`Void`@.  You should use `Void` instead
    of `X` now
-}
type X = Void
{-# DEPRECATED X "Use Data.Void.Void instead" #-}

traverseWithIndex_ :: Applicative f => (Int -> a -> f b) -> Seq a -> f ()
traverseWithIndex_ k xs = Foldable.sequenceA_ (Data.Sequence.mapWithIndex k xs)

axiom :: Const -> Either (TypeError s a) Const
axiom Type = return Kind
axiom Kind = return Sort
axiom Sort = Left (TypeError Dhall.Context.empty (Const Sort) Untyped)

rule :: Const -> Const -> Const
rule Type Type = Type
rule Kind Type = Type
rule Sort Type = Type
rule Type Kind = Kind
rule Kind Kind = Kind
rule Sort Kind = Sort
rule Type Sort = Sort
rule Kind Sort = Sort
rule Sort Sort = Sort

{-| Type-check an expression and return the expression's type if type-checking
    succeeds or an error if type-checking fails

    `typeWith` does not necessarily normalize the type since full normalization
    is not necessary for just type-checking.  If you actually care about the
    returned type then you may want to `Dhall.Core.normalize` it afterwards.

    The supplied `Context` records the types of the names in scope. If
    these are ill-typed, the return value may be ill-typed.
-}
typeWith :: Context (Expr s X) -> Expr s X -> Either (TypeError s X) (Expr s X)
typeWith ctx expr = do
    checkContext ctx
    typeWithA absurd ctx expr

{-| Function that converts the value inside an `Embed` constructor into a new
    expression
-}
type Typer a = forall s. a -> Expr s a

{-| Generalization of `typeWith` that allows type-checking the `Embed`
    constructor with custom logic
-}
typeWithA
    :: (Eq a, Pretty a)
    => Typer a
    -> Context (Expr s a)
    -> Expr s a
    -> Either (TypeError s a) (Expr s a)
typeWithA tpa context expression =
    fmap (Dhall.Core.renote . Eval.quote EmptyNames) (infer tpa ctx expression)
  where
    ctx = contextToCtx context

contextToCtx :: Eq a => Context (Expr s a) -> Ctx a
contextToCtx context = loop (Dhall.Context.toList context)
  where
    loop [] =
        Ctx Empty TypesEmpty

    loop ((x, t):rest) =
        Ctx (Skip vs x) (TypesBind ts x (Eval.eval vs (Dhall.Core.denote t)))
      where
        Ctx vs ts = loop rest

ctxToContext :: Eq a => Ctx a -> Context (Expr s a)
ctxToContext (Ctx {..}) = loop types
  where
    loop (TypesBind ts x t) = Dhall.Context.insert x t' (loop ts)
      where
        ns = typesToNames ts

        t' = Dhall.Core.renote (Eval.quote ns t)
    loop TypesEmpty = Dhall.Context.empty

typesToNames :: Types a -> Names
typesToNames (TypesBind ts x _) = Bind ns x
  where
    ns = typesToNames ts
typesToNames TypesEmpty = EmptyNames

data Types a = TypesEmpty | TypesBind !(Types a) {-# UNPACK #-} !Text (Val a)

data Ctx a = Ctx { values :: !(Environment a), types :: !(Types a) }

addType :: Text -> Val a -> Ctx a -> Ctx a
addType x t (Ctx vs ts) = Ctx (Skip vs x) (TypesBind ts x t)

addTypeValue :: Text -> Val a -> Val a -> Ctx a -> Ctx a
addTypeValue x t v (Ctx vs ts) = Ctx (Extend vs x v) (TypesBind ts x t)

fresh :: Ctx a -> Text -> Val a
fresh Ctx{..} x = VVar x (Eval.countNames x (Eval.envNames values))

{-| `typeWithA` is implemented internally in terms of @infer@ in order to speed
    up equivalence checking.

    Specifically, we extend the `Context` to become a @Ctx@, which can store
    the entire contents of a `let` expression (i.e. the type *and* the value
    of the bound variable).  By storing this extra information in the @Ctx@ we
    no longer need to substitute `let` expressions at all (which is very
    expensive!).

    However, this means that we need to use `Dhall.Eval.conv` to perform
    equivalence checking instead of `Dhall.Core.judgmentallyEqual` since
    only `Dhall.Core.judgmentallyEqual` is unable to use the information stored
    in the extended context for accurate equivalence checking.
-}
infer
    :: forall a s
    .  (Eq a, Pretty a)
    => Typer a
    -> Ctx a
    -> Expr s a
    -> Either (TypeError s a) (Val a)
infer typer = loop
  where
    {- The convention for primes (i.e. `'`s) is:

       * No primes  (`x`  ): An `Expr` that has not been `eval`ed yet
       * One prime  (`x'` ): A  `Val`
       * Two primes (`x''`): An `Expr` generated from `quote`ing a `Val`
    -}
    loop :: Ctx a -> Expr s a -> Either (TypeError s a) (Val a)
    loop ctx@Ctx{..} expression = case expression of
        Const c ->
            fmap VConst (axiom c)

        Var (V x0 n0) -> do
            let go TypesEmpty _ =
                    die (UnboundVariable x0)
                go (TypesBind ts x t) n
                    | x == x0   = if n == 0 then return t else go ts (n - 1)
                    | otherwise = go ts n

            go types n0

        Lam _ (FunctionBinding { functionBindingVariable = x, functionBindingAnnotation = _A}) b -> do
            tA' <- loop ctx _A

            case tA' of
                VConst _ -> return ()
                _        -> die (InvalidInputType _A)

            let _A' = eval values _A

            let ctx' = addType x _A' ctx

            _B' <- loop ctx' b

            let _B'' = quote (Bind (Eval.envNames values) x) _B'

            tB' <- loop ctx' (Dhall.Core.renote _B'')

            case tB' of
                VConst _ -> return ()
                _        -> die (InvalidOutputType _B'')

            return (VHPi x _A' (\u -> Eval.eval (Extend values x u) _B''))

        Pi _ x _A _B -> do
            tA' <- loop ctx _A

            kA <- case tA' of
                VConst kA -> return kA
                _         -> die (InvalidInputType _A)

            let _A' = eval values _A

            let ctx' = addType x _A' ctx

            tB' <- loop ctx' _B

            kB <- case tB' of
                VConst kB -> return kB
                _         -> die (InvalidOutputType _B)

            return (VConst (rule kA kB))

        App f a -> do
            tf' <- loop ctx f

            case Eval.toVHPi tf' of
                Just (_x, _A₀', _B') -> do
                    _A₁' <- loop ctx a

                    if Eval.conv values _A₀' _A₁'
                        then do
                            let a' = eval values a

                            return (_B' a')

                        else do
                            let _A₀'' = quote names _A₀'
                            let _A₁'' = quote names _A₁'
                            die (TypeMismatch f _A₀'' a _A₁'')
                Nothing ->
                    die (NotAFunction f (quote names tf'))

        Let (Binding { value = a₀, variable = x, ..}) body -> do
            let a₀' = eval values a₀

            ctxNew <- case annotation of
                Nothing -> do
                    _A' <- loop ctx a₀

                    return (addTypeValue x _A' a₀' ctx)
                Just (_, _A₀) -> do
                    _ <- loop ctx _A₀

                    let _A₀' = eval values _A₀

                    _A₁' <- loop ctx a₀

                    if Eval.conv values _A₀' _A₁'
                        then
                            return ()

                        else do
                            let _A₀'' = quote names _A₀'
                            let _A₁'' = quote names _A₁'
                            Left (TypeError context a₀ (AnnotMismatch a₀ _A₀'' _A₁''))

                    return (addTypeValue x _A₀' a₀' ctx)

            loop ctxNew body

        Annot t _T₀ -> do
            case Dhall.Core.denote _T₀ of
                Const _ -> return ()
                _       -> do
                    _ <- loop ctx _T₀

                    return ()

            let _T₀' = eval values _T₀

            _T₁' <- loop ctx t

            if Eval.conv values _T₀' _T₁'
                then
                    return _T₁'

                else do
                    let _T₀'' = quote names _T₀'
                    let _T₁'' = quote names _T₁'
                    die (AnnotMismatch t _T₀'' _T₁'')

        Bool ->
            return (VConst Type)

        BoolLit _ ->
            return VBool

        BoolAnd l r -> do
            tl' <- loop ctx l

            case tl' of
                VBool -> return ()
                _     -> die (CantAnd l (quote names tl'))

            tr' <- loop ctx r

            case tr' of
                VBool -> return ()
                _     -> die (CantAnd r (quote names tr'))

            return VBool

        BoolOr l r -> do
            tl' <- loop ctx l

            case tl' of
                VBool -> return ()
                _     -> die (CantOr l (quote names tl'))

            tr' <- loop ctx r

            case tr' of
                VBool -> return ()
                _     -> die (CantOr r (quote names tr'))

            return VBool

        BoolEQ l r -> do
            tl' <- loop ctx l

            case tl' of
                VBool -> return ()
                _     -> die (CantEQ l (quote names tl'))

            tr' <- loop ctx r

            case tr' of
                VBool -> return ()
                _     -> die (CantEQ r (quote names tr'))

            return VBool

        BoolNE l r -> do
            tl' <- loop ctx l

            case tl' of
                VBool -> return ()
                _     -> die (CantNE l (quote names tl'))

            tr' <- loop ctx r

            case tr' of
                VBool -> return ()
                _     -> die (CantNE r (quote names tr'))

            return VBool

        BoolIf t l r -> do
            tt' <- loop ctx t

            case tt' of
                VBool -> return ()
                _     -> die (InvalidPredicate t (quote names tt'))

            _L' <- loop ctx l

            _R' <- loop ctx r

            _ <- loop ctx (quote names _L')

            let _L'' = quote names _L'

            _ <- loop ctx (quote names _R')

            let _R'' = quote names _R'

            if Eval.conv values _L' _R'
                then return ()
                else die (IfBranchMismatch l r _L'' _R'')

            return _L'

        Natural ->
            return (VConst Type)

        NaturalLit _ ->
            return VNatural

        NaturalFold ->
            return
                (   VNatural
                ~>  VHPi "natural" (VConst Type) (\natural ->
                        VHPi "succ" (natural ~> natural) (\_succ ->
                            VHPi "zero" natural (\_zero ->
                                natural
                            )
                        )
                    )
                )

        NaturalBuild ->
            return
                (   VHPi "natural" (VConst Type) (\natural ->
                        VHPi "succ" (natural ~> natural) (\_succ ->
                            VHPi "zero" natural (\_zero ->
                                natural
                            )
                        )
                    )
                ~>  VNatural
                )

        NaturalIsZero ->
            return (VNatural ~> VBool)

        NaturalEven ->
            return (VNatural ~> VBool)

        NaturalOdd ->
            return (VNatural ~> VBool)

        NaturalToInteger ->
            return (VNatural ~> VInteger)

        NaturalShow ->
            return (VNatural ~> VText)

        NaturalSubtract ->
            return (VNatural ~> VNatural ~> VNatural)

        NaturalPlus l r -> do
            tl' <- loop ctx l

            case tl' of
                VNatural -> return ()
                _        -> die (CantAdd l (quote names tl'))

            tr' <- loop ctx r

            case tr' of
                VNatural -> return ()
                _        -> die (CantAdd r (quote names tr'))

            return VNatural

        NaturalTimes l r -> do
            tl' <- loop ctx l

            case tl' of
                VNatural -> return ()
                _        -> die (CantMultiply l (quote names tl'))

            tr' <- loop ctx r

            case tr' of
                VNatural -> return ()
                _        -> die (CantMultiply r (quote names tr'))

            return VNatural

        Integer ->
            return (VConst Type)

        IntegerLit _ ->
            return VInteger

        IntegerClamp ->
            return (VInteger ~> VNatural)

        IntegerNegate ->
            return (VInteger ~> VInteger)

        IntegerShow ->
            return (VInteger ~> VText)

        IntegerToDouble ->
            return (VInteger ~> VDouble)

        Double ->
            return (VConst Type)

        DoubleLit _ ->
            return VDouble

        DoubleShow ->
            return (VDouble ~> VText)

        Text ->
            return (VConst Type)

        TextLit (Chunks xys _) -> do
            let process (_, y) = do
                    _Y' <- loop ctx y

                    case _Y' of
                        VText -> return ()
                        _     -> die (CantInterpolate y (quote names _Y'))

            mapM_ process xys

            return VText

        TextAppend l r -> do
            tl' <- loop ctx l

            case tl' of
                VText -> return ()
                _     -> die (CantTextAppend l (quote names tl'))

            tr' <- loop ctx r

            case tr' of
                VText -> return ()
                _     -> die (CantTextAppend r (quote names tr'))

            return VText

        TextReplace ->
            return
                (   VHPi "needle" VText  (\_needle ->
                        VHPi "replacement" VText (\_replacement ->
                            VHPi "haystack" VText (\_haystack ->
                                VText
                            )
                        )
                    )
                )
        TextShow ->
            return (VText ~> VText)

        Date ->
            return (VConst Type)

        DateLiteral _ ->
            return VDate

        Time ->
            return (VConst Type)

        TimeLiteral _ _ ->
            return VTime

        TimeZone ->
            return (VConst Type)

        TimeZoneLiteral _ ->
            return VTimeZone

        List ->
            return (VConst Type ~> VConst Type)

        ListLit Nothing ts₀ ->
            case Data.Sequence.viewl ts₀ of
                t₀ :< ts₁ -> do
                    _T₀' <- loop ctx t₀

                    let _T₀'' = quote names _T₀'

                    tT₀' <- loop ctx _T₀''

                    case tT₀' of
                        VConst Type -> return ()
                        _           -> die (InvalidListType (App List _T₀''))

                    let process i t₁ = do
                            _T₁' <- loop ctx t₁

                            if Eval.conv values _T₀' _T₁'
                                then
                                    return ()

                                else do
                                    let _T₀'' = quote names _T₀'
                                    let _T₁'' = quote names _T₁'

                                    -- Carefully note that we don't use `die`
                                    -- here so that the source span is narrowed
                                    -- to just the offending element
                                    let err = MismatchedListElements (i+1) _T₀'' t₁ _T₁''

                                    Left (TypeError context t₁ err)

                    traverseWithIndex_ process ts₁

                    return (VList _T₀')

                _ ->
                    die MissingListType

        ListLit (Just _T₀) ts ->
            if Data.Sequence.null ts
                then do
                    _ <- loop ctx _T₀

                    let _T₀' = eval values _T₀

                    let _T₀'' = quote names _T₀'

                    case _T₀' of
                        VList _ -> return _T₀'
                        _       -> die (InvalidListType _T₀'')

                -- See https://github.com/dhall-lang/dhall-haskell/issues/1359.
                else die ListLitInvariant

        ListAppend x y -> do
            tx' <- loop ctx x

            _A₀' <- case tx' of
                VList _A₀' -> return _A₀'
                _          -> die (CantListAppend x (quote names tx'))

            ty' <- loop ctx y

            _A₁' <- case ty' of
                VList _A₁' -> return _A₁'
                _          -> die (CantListAppend y (quote names ty'))

            if Eval.conv values _A₀' _A₁'
                then return ()
                else do
                    let _A₀'' = quote names _A₀'
                    let _A₁'' = quote names _A₁'
                    die (ListAppendMismatch _A₀'' _A₁'')

            return (VList _A₀')

        ListBuild ->
            return
                (   VHPi "a" (VConst Type) (\a ->
                            VHPi "list" (VConst Type) (\list ->
                                VHPi "cons" (a ~> list ~> list) (\_cons ->
                                    (VHPi "nil" list (\_nil -> list))
                                )
                            )
                        ~>  VList a
                    )
                )

        ListFold ->
            return
                (   VHPi "a" (VConst Type) (\a ->
                            VList a
                        ~>  VHPi "list" (VConst Type) (\list ->
                                VHPi "cons" (a ~> list ~> list) (\_cons ->
                                    (VHPi "nil" list (\_nil -> list))
                                )
                            )
                    )
                )

        ListLength ->
            return (VHPi "a" (VConst Type) (\a -> VList a ~> VNatural))

        ListHead ->
            return (VHPi "a" (VConst Type) (\a -> VList a ~> VOptional a))

        ListLast ->
            return (VHPi "a" (VConst Type) (\a -> VList a ~> VOptional a))

        ListIndexed ->
            return
                (   VHPi "a" (VConst Type) (\a ->
                            VList a
                        ~>  VList
                                (VRecord
                                    (Dhall.Map.unorderedFromList
                                        [ ("index", VNatural)
                                        , ("value", a       )
                                        ]
                                    )
                                )
                    )
                )
        ListReverse ->
            return (VHPi "a" (VConst Type) (\a -> VList a ~> VList a))

        Optional ->
            return (VConst Type ~> VConst Type)

        None ->
            return (VHPi "A" (VConst Type) (\_A -> VOptional _A))

        Some a -> do
            _A' <- loop ctx a

            tA' <- loop ctx (quote names _A')

            case tA' of
                VConst Type -> return ()
                _           -> do
                   let _A'' = quote names _A'
                   let tA'' = quote names tA'

                   die (InvalidSome a _A'' tA'')

            return (VOptional _A')

        Record xTs -> do
            let process x (RecordField {recordFieldValue = _T}) = do
                    tT' <- lift (loop ctx _T)

                    case tT' of
                        VConst c -> tell (Max c)
                        _        -> lift (die (InvalidFieldType x _T))

            Max c <- execWriterT (Dhall.Map.unorderedTraverseWithKey_ process xTs)

            return (VConst c)

        RecordLit xts -> do
            let process t = do
                    _T' <- loop ctx $ recordFieldValue t

                    let _T'' = quote names _T'

                    _ <- loop ctx _T''

                    return _T'

            xTs <- traverse process (Dhall.Map.sort xts)

            return (VRecord xTs)

        Union xTs -> do
            let process _ Nothing =
                    return mempty

                process x₁ (Just _T₁) = do
                    tT₁' <- loop ctx _T₁

                    case tT₁' of
                        VConst c -> return (Max c)
                        _        -> die (InvalidAlternativeType x₁ _T₁)

            Max c <- fmap Foldable.fold (Dhall.Map.unorderedTraverseWithKey process xTs)
            return (VConst c)
        Combine _ mk l r -> do
            _L' <- loop ctx l

            let l'' = quote names (eval values l)

            _R' <- loop ctx r

            let r'' = quote names (eval values r)

            xLs' <- case _L' of
                VRecord xLs' ->
                    return xLs'

                _ -> do
                    let _L'' = quote names _L'

                    case mk of
                        Nothing -> die (MustCombineARecord '∧' l'' _L'')
                        Just t  -> die (InvalidDuplicateField t l _L'')

            xRs' <- case _R' of
                VRecord xRs' ->
                    return xRs'

                _ -> do
                    let _R'' = quote names _R'

                    case mk of
                        Nothing -> die (MustCombineARecord '∧' r'' _R'')
                        Just t  -> die (InvalidDuplicateField t r _R'')

            let combineTypes xs xLs₀' xRs₀' = do
                    let combine x (VRecord xLs₁') (VRecord xRs₁') =
                            combineTypes (x : xs) xLs₁' xRs₁'

                        combine x _ _ =
                            case mk of
                                Nothing -> die (FieldCollision (NonEmpty.reverse (x :| xs)))
                                Just t  -> die (DuplicateFieldCannotBeMerged (t :| reverse (x : xs)))

                    let xEs =
                            Dhall.Map.outerJoin Right Right combine xLs₀' xRs₀'

                    xTs <- Dhall.Map.unorderedTraverseWithKey (\_x _E -> _E) xEs

                    return (VRecord xTs)

            combineTypes [] xLs' xRs'

        CombineTypes _ l r -> do
            _L' <- loop ctx l

            let l' = eval values l

            let l'' = quote names l'

            cL <- case _L' of
                VConst cL -> return cL
                _         -> die (CombineTypesRequiresRecordType l l'')

            _R' <- loop ctx r

            let r' = eval values r

            let r'' = quote names r'

            cR <- case _R' of
                VConst cR -> return cR
                _         -> die (CombineTypesRequiresRecordType r r'')

            let c = max cL cR

            xLs' <- case l' of
                VRecord xLs' -> return xLs'
                _            -> die (CombineTypesRequiresRecordType l l'')

            xRs' <- case r' of
                VRecord xRs' -> return xRs'
                _            -> die (CombineTypesRequiresRecordType r r'')

            let combineTypes xs xLs₀' xRs₀' = do
                    let combine x (VRecord xLs₁') (VRecord xRs₁') =
                            combineTypes (x : xs) xLs₁' xRs₁'

                        combine x _ _ =
                            die (FieldTypeCollision (NonEmpty.reverse (x :| xs)))

                    let mL = Dhall.Map.toMap xLs₀'
                    let mR = Dhall.Map.toMap xRs₀'

                    Foldable.sequence_ (Data.Map.intersectionWithKey combine mL mR)

            combineTypes [] xLs' xRs'

            return (VConst c)

        Prefer _ a l r -> do
            _L' <- loop ctx l

            _R' <- loop ctx r

            xLs' <- case _L' of
                VRecord xLs' -> return xLs'

                _            -> do
                    let _L'' = quote names _L'

                    let l'' = quote names (eval values l)

                    case a of
                        PreferFromWith withExpression ->
                            die (MustUpdateARecord withExpression l'' _L'')
                        _ ->
                            die (MustCombineARecord '⫽' l'' _L'')

            xRs' <- case _R' of
                VRecord xRs' -> return xRs'

                _            -> do
                    let _R'' = quote names _R'

                    let r'' = quote names (eval values r)

                    die (MustCombineARecord '⫽' r'' _R'')

            return (VRecord (Dhall.Map.union xRs' xLs'))

        RecordCompletion l r -> do
            _L' <- loop ctx l

            case _L' of
                VRecord xLs'
                  | not (Dhall.Map.member "default" xLs')
                     -> die (InvalidRecordCompletion "default" l)
                  | not (Dhall.Map.member "Type" xLs')
                     -> die (InvalidRecordCompletion "Type" l)
                  | otherwise
                     -> loop ctx (Annot (Prefer mempty PreferFromCompletion (Field l def) r) (Field l typ))
                _ -> die (CompletionSchemaMustBeARecord l (quote names _L'))

              where
                def = Syntax.makeFieldSelection "default"
                typ = Syntax.makeFieldSelection "Type"
        Merge t u mT₁ -> do
            _T' <- loop ctx t

            yTs' <- case _T' of
                VRecord yTs' ->
                    return yTs'

                _ -> do
                    let _T'' = quote names _T'

                    die (MustMergeARecord t _T'')

            _U' <- loop ctx u

            yUs' <- case _U' of
                VUnion yUs' ->
                    return yUs'

                VOptional _O' ->
                    -- This is a bit of hack, but it allows us to reuse the
                    -- rather complex type-matching logic for Optionals.
                    return (Dhall.Map.unorderedFromList [("None", Nothing), ("Some", Just _O')])

                _ -> do
                    let _U'' = quote names _U'

                    die (MustMergeUnionOrOptional u _U'')

            let ysT = Dhall.Map.keysSet yTs'
            let ysU = Dhall.Map.keysSet yUs'

            let diffT = Data.Set.difference ysT ysU
            let diffU = Data.Set.difference ysU ysT

            if Data.Set.null diffT
                then return ()
                else die (UnusedHandler diffT)

            if Data.Set.null diffU
                then return ()
                else let (exemplar,rest) = Data.Set.deleteFindMin diffU
                     in die (MissingHandler exemplar rest)

            let match _y _T₀' Nothing =
                    return _T₀'

                match y handler' (Just _A₁') =
                    case Eval.toVHPi handler' of
                        Just (x, _A₀', _T₀') ->
                            if Eval.conv values _A₀' _A₁'
                                then do
                                    let _T₁' = _T₀' (fresh ctx x)

                                    let _T₁'' = quote names _T₁'

                                    -- x appearing in _T₁'' would indicate a disallowed
                                    -- handler type (see
                                    -- https://github.com/dhall-lang/dhall-lang/issues/749).
                                    --
                                    -- If x appears in _T₁'', quote will have given it index
                                    -- -1. Any well-typed variable has a non-negative index,
                                    -- so we can simply look for negative indices to detect x.
                                    let containsBadVar (Var (V _ n)) =
                                            n < 0

                                        containsBadVar e =
                                            Lens.Family.anyOf
                                                Dhall.Core.subExpressions
                                                containsBadVar
                                                e

                                    if containsBadVar _T₁''
                                        then do
                                            let handler'' = quote names handler'

                                            let outputType = Dhall.Core.shift 1 (V x (-1)) _T₁''

                                            die (DisallowedHandlerType y handler'' outputType x)

                                        else return _T₁'

                                else do
                                    let _A₀'' = quote names _A₀'
                                    let _A₁'' = quote names _A₁'

                                    die (HandlerInputTypeMismatch y _A₁'' _A₀'')

                        Nothing -> do
                            let handler'' = quote names handler'

                            die (HandlerNotAFunction y handler'')

            matched <-
                sequence
                    (Data.Map.intersectionWithKey match (Dhall.Map.toMap yTs') (Dhall.Map.toMap yUs'))

            let checkMatched :: Data.Map.Map Text (Val a) -> Either (TypeError s a) (Maybe (Val a))
                checkMatched = fmap (fmap snd) . Foldable.foldlM go Nothing . Data.Map.toList
                  where
                    go Nothing (y₁, _T₁') =
                        return (Just (y₁, _T₁'))

                    go yT₀'@(Just (y₀, _T₀')) (y₁, _T₁') =
                        if Eval.conv values _T₀' _T₁'
                            then return yT₀'

                            else do
                                let _T₀'' = quote names _T₀'
                                let _T₁'' = quote names _T₁'
                                die (HandlerOutputTypeMismatch y₀ _T₀'' y₁ _T₁'')

            mT₀' <- checkMatched matched

            mT₁' <- Data.Traversable.for mT₁ $ \_T₁ -> do
                _ <- loop ctx _T₁

                return (eval values _T₁)

            case (mT₀', mT₁') of
                (Nothing, Nothing) ->
                    die MissingMergeType
                (Nothing, Just _T₁') ->
                    return _T₁'
                (Just _T₀', Nothing) ->
                    return _T₀'
                (Just _T₀', Just _T₁') ->
                    if Eval.conv values _T₀' _T₁'
                        then return _T₀'

                        else do
                            let _T₀'' = quote names _T₀'
                            let _T₁'' = quote names _T₁'
                            die (AnnotMismatch (Merge t u Nothing) _T₁'' _T₀'')

        ToMap e mT₁ -> do
            _E' <- loop ctx e

            let _E'' = quote names _E'

            xTs' <- case _E' of
                VRecord xTs' -> return xTs'
                _            -> die (MustMapARecord e _E'')

            tE' <- loop ctx _E''

            let tE'' = quote names tE'

            case tE' of
                VConst Type -> return ()
                _           -> die (InvalidToMapRecordKind _E'' tE'')

            Foldable.traverse_ (loop ctx) mT₁

            let compareFieldTypes _T₀' Nothing =
                    Just (Right _T₀')

                compareFieldTypes _T₀' r@(Just (Right _T₁'))
                    | Eval.conv values _T₀' _T₁' = r
                    | otherwise = do
                        let _T₀'' = quote names _T₀'
                        let _T₁'' = quote names _T₁'

                        Just (die (HeterogenousRecordToMap _E'' _T₀'' _T₁''))

                compareFieldTypes _T₀' r@(Just (Left _)) =
                    r

            let r = appEndo (foldMap (Endo . compareFieldTypes) xTs') Nothing

            let mT₁' = fmap (eval values) mT₁

            let mapType _T' =
                    VList
                        (VRecord
                            (Dhall.Map.unorderedFromList
                                [("mapKey", VText), ("mapValue", _T')]
                            )
                        )

            case (r, mT₁') of
                (Nothing, Nothing) ->
                    die MissingToMapType
                (Just err@(Left _), _) ->
                    err
                (Just (Right _T'), Nothing) ->
                    pure (mapType _T')
                (Nothing, Just _T₁'@(VList (VRecord itemTypes)))
                   | Just _T' <- Dhall.Map.lookup "mapValue" itemTypes
                   , Eval.conv values (mapType _T') _T₁' ->
                       pure _T₁'
                (Nothing, Just _T₁') -> do
                    let _T₁'' = quote names _T₁'

                    die (InvalidToMapType _T₁'')
                (Just (Right _T'), Just _T₁')
                   | Eval.conv values (mapType _T') _T₁' ->
                       pure (mapType _T')
                   | otherwise -> do
                       let _T₁'' = quote names _T₁'

                       die (MapTypeMismatch (quote names (mapType _T')) _T₁'')

        Field e (Syntax.fieldSelectionLabel -> x) -> do
            _E' <- loop ctx e

            let _E'' = quote names _E'

            case _E' of
                VRecord xTs' ->
                    case Dhall.Map.lookup x xTs' of
                        Just _T' -> return _T'
                        Nothing  -> die (MissingField x _E'')
                _ -> do
                    let e' = eval values e

                    let e'' = quote names e'

                    case e' of
                        VUnion xTs' ->
                            case Dhall.Map.lookup x xTs' of
                                Just (Just _T') -> return (VHPi x _T' (\_ -> e'))
                                Just  Nothing   -> return e'
                                Nothing         -> die (MissingConstructor x e)

                        _ -> do
                            let text = Dhall.Pretty.Internal.docToStrictText (Dhall.Pretty.Internal.prettyLabel x)

                            die (CantAccess text e'' _E'')
        Project e (Left xs) -> do
            case duplicateElement xs of
                Just x -> do
                    die (DuplicateProjectionLabel x)
                Nothing -> do
                    return ()

            _E' <- loop ctx e

            let _E'' = quote names _E'

            case _E' of
                VRecord xTs' -> do
                    let process x =
                            case Dhall.Map.lookup x xTs' of
                                Just _T' -> return (x, _T')
                                Nothing  -> die (MissingField x _E'')

                    let adapt = VRecord . Dhall.Map.unorderedFromList

                    fmap adapt (traverse process xs)

                _ -> do
                    let text =
                            Dhall.Pretty.Internal.docToStrictText (Dhall.Pretty.Internal.prettyLabels xs)

                    die (CantProject text e _E'')

        Project e (Right s) -> do
            _E' <- loop ctx e

            let _E'' = quote names _E'

            case _E' of
                VRecord xEs' -> do
                    _ <- loop ctx s

                    let s' = eval values s

                    case s' of
                        VRecord xSs' -> do
                            let actualSubset =
                                    quote names (VRecord (Dhall.Map.intersection xEs' xSs'))

                            let expectedSubset = s

                            let process x _S' = do
                                    let _S'' = quote names _S'

                                    case Dhall.Map.lookup x xEs' of
                                        Nothing ->
                                            die (MissingField x _E'')

                                        Just _E' ->
                                            if Eval.conv values _E' _S'
                                                then return ()
                                                else die (ProjectionTypeMismatch x _E'' _S'' expectedSubset actualSubset)

                            Dhall.Map.unorderedTraverseWithKey_ process xSs'

                            return s'

                        _ ->
                            die (CantProjectByExpression s)

                _ -> do
                    let text = Dhall.Core.pretty s

                    die (CantProject text e s)

        Assert _T -> do
            _ <- loop ctx _T

            let _T' = eval values _T

            case _T' of
                VEquivalent x' y' -> do
                    let x'' = quote names x'
                    let y'' = quote names y'

                    if Eval.conv values x' y'
                        then return _T'
                        else die (AssertionFailed x'' y'')

                _ ->
                    die (NotAnEquivalence _T)

        Equivalent _ x y -> do
            _A₀' <- loop ctx x

            let _A₀'' = quote names _A₀'

            tA₀' <- loop ctx _A₀''

            case tA₀' of
                VConst Type -> return ()
                _          -> die (IncomparableExpression x)

            _A₁' <- loop ctx y

            let _A₁'' = quote names _A₁'

            tA₁' <- loop ctx _A₁''

            case tA₁' of
                VConst Type -> return ()
                _           -> die (IncomparableExpression y)

            if Eval.conv values _A₀' _A₁'
                then return ()
                else die (EquivalenceTypeMismatch x _A₀'' y _A₁'')

            return (VConst Type)

        With e₀ ks₀ v₀ -> do
            tE₀' <- loop ctx e₀

            -- The purpose of this inner loop is to ensure that we only need to
            -- typecheck the record once
            let with tE' ks v = do
                    kTs' <- case tE' of
                        VRecord kTs' -> return kTs'
                        _            -> die (NotWithARecord e₀ (quote names tE'))

                    case ks of
                        k :| [] -> do
                            tV' <- loop ctx v

                            return (VRecord (Dhall.Map.insert k tV' kTs'))
                        k₀ :| k₁ : ks' -> do
                            let _T =
                                    case Dhall.Map.lookup k₀ kTs' of
                                        Just _T' -> _T'
                                        Nothing  -> VRecord mempty

                            tV' <- with _T (k₁ :| ks') v

                            return (VRecord (Dhall.Map.insert k₀ tV' kTs'))

            with tE₀' ks₀ v₀

        Note s e ->
            case loop ctx e of
                Left (TypeError ctx' (Note s' e') m) ->
                    Left (TypeError ctx' (Note s' e') m)
                Left (TypeError ctx'          e'  m) ->
                    Left (TypeError ctx' (Note s  e') m)
                Right r ->
                    Right r

        ImportAlt l _r ->
            loop ctx l

        Embed p ->
            return (eval values (typer p))
      where
        die err = Left (TypeError context expression err)

        context = ctxToContext ctx

        names = typesToNames types

        eval vs e = Eval.eval vs (Dhall.Core.denote e)

        quote ns value = Dhall.Core.renote (Eval.quote ns value)

{-| `typeOf` is the same as `typeWith` with an empty context, meaning that the
    expression must be closed (i.e. no free variables), otherwise type-checking
    will fail.
-}
typeOf :: Expr s X -> Either (TypeError s X) (Expr s X)
typeOf = typeWith Dhall.Context.empty

-- | The specific type error
data TypeMessage s a
    = UnboundVariable Text
    | InvalidInputType (Expr s a)
    | InvalidOutputType (Expr s a)
    | NotAFunction (Expr s a) (Expr s a)
    | TypeMismatch (Expr s a) (Expr s a) (Expr s a) (Expr s a)
    | AnnotMismatch (Expr s a) (Expr s a) (Expr s a)
    | Untyped
    | MissingListType
    | MismatchedListElements Int (Expr s a) (Expr s a) (Expr s a)
    | InvalidListElement Int (Expr s a) (Expr s a) (Expr s a)
    | InvalidListType (Expr s a)
    | ListLitInvariant
    | InvalidSome (Expr s a) (Expr s a) (Expr s a)
    | InvalidPredicate (Expr s a) (Expr s a)
    | IfBranchMismatch (Expr s a) (Expr s a) (Expr s a) (Expr s a)
    | InvalidFieldType Text (Expr s a)
    | InvalidAlternativeType Text (Expr s a)
    | ListAppendMismatch (Expr s a) (Expr s a)
    | MustUpdateARecord (Expr s a) (Expr s a) (Expr s a)
    | MustCombineARecord Char (Expr s a) (Expr s a)
    | InvalidDuplicateField Text (Expr s a) (Expr s a)
    | InvalidRecordCompletion Text (Expr s a)
    | CompletionSchemaMustBeARecord (Expr s a) (Expr s a)
    | CombineTypesRequiresRecordType (Expr s a) (Expr s a)
    | RecordTypeMismatch Const Const (Expr s a) (Expr s a)
    | DuplicateFieldCannotBeMerged (NonEmpty Text)
    | FieldCollision (NonEmpty Text)
    | FieldTypeCollision (NonEmpty Text)
    | MustMergeARecord (Expr s a) (Expr s a)
    | MustMergeUnionOrOptional (Expr s a) (Expr s a)
    | MustMapARecord (Expr s a) (Expr s a)
    | InvalidToMapRecordKind (Expr s a) (Expr s a)
    | HeterogenousRecordToMap (Expr s a) (Expr s a) (Expr s a)
    | InvalidToMapType (Expr s a)
    | MapTypeMismatch (Expr s a) (Expr s a)
    | MissingToMapType
    | UnusedHandler (Set Text)
    | MissingHandler Text (Set Text)
    | HandlerInputTypeMismatch Text (Expr s a) (Expr s a)
    | DisallowedHandlerType Text (Expr s a) (Expr s a) Text
    | HandlerOutputTypeMismatch Text (Expr s a) Text (Expr s a)
    | InvalidHandlerOutputType Text (Expr s a) (Expr s a)
    | MissingMergeType
    | HandlerNotAFunction Text (Expr s a)
    | CantAccess Text (Expr s a) (Expr s a)
    | CantProject Text (Expr s a) (Expr s a)
    | CantProjectByExpression (Expr s a)
    | DuplicateProjectionLabel Text
    | MissingField Text (Expr s a)
    | MissingConstructor Text (Expr s a)
    | ProjectionTypeMismatch Text (Expr s a) (Expr s a) (Expr s a) (Expr s a)
    | AssertionFailed (Expr s a) (Expr s a)
    | NotAnEquivalence (Expr s a)
    | IncomparableExpression (Expr s a)
    | EquivalenceTypeMismatch (Expr s a) (Expr s a) (Expr s a) (Expr s a)
    | NotWithARecord (Expr s a) (Expr s a)
    | CantAnd (Expr s a) (Expr s a)
    | CantOr (Expr s a) (Expr s a)
    | CantEQ (Expr s a) (Expr s a)
    | CantNE (Expr s a) (Expr s a)
    | CantInterpolate (Expr s a) (Expr s a)
    | CantTextAppend (Expr s a) (Expr s a)
    | CantListAppend (Expr s a) (Expr s a)
    | CantAdd (Expr s a) (Expr s a)
    | CantMultiply (Expr s a) (Expr s a)
    deriving (Show)

formatHints :: [Doc Ann] -> Doc Ann
formatHints hints = vsep (map format hints)
  where
    format hint = "\n\n\ESC[1;33mHint\ESC[0m: " <> hint

shortTypeMessage :: (Eq a, Pretty a) => TypeMessage s a -> Doc Ann
shortTypeMessage msg =
    "\ESC[1;31mError\ESC[0m: " <> short <> formatHints hints <> "\n"
  where
    ErrorMessages {..} = prettyTypeMessage msg

longTypeMessage :: (Eq a, Pretty a) => TypeMessage s a -> Doc Ann
longTypeMessage msg =
        "\ESC[1;31mError\ESC[0m: " <> short <> formatHints hints <> "\n"
    <>  "\n"
    <>  long
  where
    ErrorMessages {..} = prettyTypeMessage msg

{-| Output of `prettyTypeMessage`, containing short- and long-form error
    messages
-}
data ErrorMessages = ErrorMessages
    { short :: Doc Ann
    -- ^ Default succinct 1-line explanation of what went wrong
    , hints :: [Doc Ann]
    -- ^ Possibly-empty hints based on specific types involved in the error
    , long  :: Doc Ann
    -- ^ Longer and more detailed explanation of the error
    }

_NOT :: Doc ann
_NOT = "\ESC[1mnot\ESC[0m"

insert :: Pretty a => a -> Doc Ann
insert = Dhall.Util.insert

emptyRecordTypeHint :: (Eq a, Pretty a) => Expr s a -> [Doc Ann]
emptyRecordTypeHint expr =
    if Eval.judgmentallyEqual expr (Record mempty) then
        ["{} is the empty record type, use {=} for the empty record value"]
    else []

-- | Convert a `TypeMessage` to short- and long-form `ErrorMessages`
prettyTypeMessage :: (Eq a, Pretty a) => TypeMessage s a -> ErrorMessages
prettyTypeMessage (UnboundVariable x) = ErrorMessages {..}
  -- We do not need to print variable name here. For the discussion see:
  -- https://github.com/dhall-lang/dhall-haskell/pull/116
  where
    short = "Unbound variable: " <> Pretty.pretty x
    
    hints = []

    long =
        "Explanation: Expressions can only reference previously introduced (i.e. “bound”)\n\
        \variables that are still “in scope”                                             \n\
        \                                                                                \n\
        \For example, the following valid expressions introduce a “bound” variable named \n\
        \❰x❱:                                                                            \n\
        \                                                                                \n\
        \                                                                                \n\
        \    ┌─────────────────┐                                                         \n\
        \    │ λ(x : Bool) → x │  Anonymous functions introduce “bound” variables        \n\
        \    └─────────────────┘                                                         \n\
        \        ⇧                                                                       \n\
        \        This is the bound variable                                              \n\
        \                                                                                \n\
        \                                                                                \n\
        \    ┌─────────────────┐                                                         \n\
        \    │ let x = 1 in x  │  ❰let❱ expressions introduce “bound” variables          \n\
        \    └─────────────────┘                                                         \n\
        \          ⇧                                                                     \n\
        \          This is the bound variable                                            \n\
        \                                                                                \n\
        \                                                                                \n\
        \However, the following expressions are not valid because they all reference a   \n\
        \variable that has not been introduced yet (i.e. an “unbound” variable):         \n\
        \                                                                                \n\
        \                                                                                \n\
        \    ┌─────────────────┐                                                         \n\
        \    │ λ(x : Bool) → y │  The variable ❰y❱ hasn't been introduced yet            \n\
        \    └─────────────────┘                                                         \n\
        \                    ⇧                                                           \n\
        \                    This is the unbound variable                                \n\
        \                                                                                \n\
        \                                                                                \n\
        \    ┌──────────────────────────┐                                                \n\
        \    │ (let x = True in x) && x │  ❰x❱ is undefined outside the parentheses      \n\
        \    └──────────────────────────┘                                                \n\
        \                             ⇧                                                  \n\
        \                             This is the unbound variable                       \n\
        \                                                                                \n\
        \                                                                                \n\
        \    ┌────────────────┐                                                          \n\
        \    │ let x = x in x │  The definition for ❰x❱ cannot reference itself          \n\
        \    └────────────────┘                                                          \n\
        \              ⇧                                                                 \n\
        \              This is the unbound variable                                      \n\
        \                                                                                \n\
        \                                                                                \n\
        \Some common reasons why you might get this error:                               \n\
        \                                                                                \n\
        \● You misspell a variable name, like this:                                      \n\
        \                                                                                \n\
        \                                                                                \n\
        \    ┌────────────────────────────────────────────────────┐                      \n\
        \    │ λ(empty : Bool) → if emty then \"Empty\" else \"Full\" │                      \n\
        \    └────────────────────────────────────────────────────┘                      \n\
        \                           ⇧                                                    \n\
        \                           Typo                                                 \n\
        \                                                                                \n\
        \                                                                                \n\
        \● You misspell a reserved identifier, like this:                                \n\
        \                                                                                \n\
        \                                                                                \n\
        \    ┌──────────────────────────┐                                                \n\
        \    │ foral (a : Type) → a → a │                                                \n\
        \    └──────────────────────────┘                                                \n\
        \      ⇧                                                                         \n\
        \      Typo                                                                      \n\
        \                                                                                \n\
        \                                                                                \n\
        \● You tried to define a recursive value, like this:                             \n\
        \                                                                                \n\
        \                                                                                \n\
        \    ┌────────────────────┐                                                      \n\
        \    │ let x = x + 1 in x │                                                      \n\
        \    └────────────────────┘                                                      \n\
        \              ⇧                                                                 \n\
        \              Recursive definitions are not allowed                             \n\
        \                                                                                \n\
        \                                                                                \n\
        \● You accidentally forgot a ❰λ❱ or ❰∀❱/❰forall❱                                 \n\
        \                                                                                \n\
        \                                                                                \n\
        \        Unbound variable                                                        \n\
        \        ⇩                                                                       \n\
        \    ┌─────────────────┐                                                         \n\
        \    │  (x : Bool) → x │                                                         \n\
        \    └─────────────────┘                                                         \n\
        \      ⇧                                                                         \n\
        \      A ❰λ❱ here would transform this into a valid anonymous function           \n\
        \                                                                                \n\
        \                                                                                \n\
        \        Unbound variable                                                        \n\
        \        ⇩                                                                       \n\
        \    ┌────────────────────┐                                                      \n\
        \    │  (x : Bool) → Bool │                                                      \n\
        \    └────────────────────┘                                                      \n\
        \      ⇧                                                                         \n\
        \      A ❰∀❱ or ❰forall❱ here would transform this into a valid function type    \n\
        \                                                                                \n\
        \                                                                                \n\
        \● You forgot to prefix a file path with ❰./❱:                                   \n\
        \                                                                                \n\
        \                                                                                \n\
        \    ┌────────────────────┐                                                      \n\
        \    │ path/to/file.dhall │                                                      \n\
        \    └────────────────────┘                                                      \n\
        \      ⇧                                                                         \n\
        \      This should be ❰./path/to/file.dhall❱                                     \n"

prettyTypeMessage (InvalidInputType expr) = ErrorMessages {..}
  where
    short = "Invalid function input"
    
    hints = []

    long =
        "Explanation: A function can accept an input “term” that has a given “type”, like\n\
        \this:                                                                           \n\
        \                                                                                \n\
        \                                                                                \n\
        \        This is the input term that the function accepts                        \n\
        \        ⇩                                                                       \n\
        \    ┌───────────────────────┐                                                   \n\
        \    │ ∀(x : Natural) → Bool │  This is the type of a function that accepts an   \n\
        \    └───────────────────────┘  input term named ❰x❱ that has type ❰Natural❱     \n\
        \            ⇧                                                                   \n\
        \            This is the type of the input term                                  \n\
        \                                                                                \n\
        \                                                                                \n\
        \    ┌────────────────┐                                                          \n\
        \    │ Bool → Natural │  This is the type of a function that accepts an anonymous\n\
        \    └────────────────┘  input term that has type ❰Bool❱                         \n\
        \      ⇧                                                                         \n\
        \      This is the type of the input term                                        \n\
        \                                                                                \n\
        \                                                                                \n\
        \... or a function can accept an input “type” that has a given “kind”, like this:\n\
        \                                                                                \n\
        \                                                                                \n\
        \        This is the input type that the function accepts                        \n\
        \        ⇩                                                                       \n\
        \    ┌────────────────────┐                                                      \n\
        \    │ ∀(a : Type) → Type │  This is the type of a function that accepts an input\n\
        \    └────────────────────┘  type named ❰a❱ that has kind ❰Type❱                 \n\
        \            ⇧                                                                   \n\
        \            This is the kind of the input type                                  \n\
        \                                                                                \n\
        \                                                                                \n\
        \    ┌──────────────────────┐                                                    \n\
        \    │ (Type → Type) → Type │  This is the type of a function that accepts an    \n\
        \    └──────────────────────┘  anonymous input type that has kind ❰Type → Type❱  \n\
        \       ⇧                                                                        \n\
        \       This is the kind of the input type                                       \n\
        \                                                                                \n\
        \                                                                                \n\
        \Other function inputs are " <> _NOT <> " valid, like this:                      \n\
        \                                                                                \n\
        \                                                                                \n\
        \    ┌──────────────┐                                                            \n\
        \    │ ∀(x : 1) → x │  ❰1❱ is a “term” and not a “type” nor a “kind” so ❰x❱      \n\
        \    └──────────────┘  cannot have “type” ❰1❱ or “kind” ❰1❱                      \n\
        \            ⇧                                                                   \n\
        \            This is not a type or kind                                          \n\
        \                                                                                \n\
        \                                                                                \n\
        \    ┌──────────┐                                                                \n\
        \    │ True → x │  ❰True❱ is a “term” and not a “type” nor a “kind” so the       \n\
        \    └──────────┘  anonymous input cannot have “type” ❰True❱ or “kind” ❰True❱    \n\
        \      ⇧                                                                         \n\
        \      This is not a type or kind                                                \n\
        \                                                                                \n\
        \                                                                                \n\
        \You annotated a function input with the following expression:                   \n\
        \                                                                                \n\
        \" <> txt <> "\n\
        \                                                                                \n\
        \... which is neither a type nor a kind                                          \n"
      where
        txt = insert expr

prettyTypeMessage (InvalidOutputType expr) = ErrorMessages {..}
  where
    short = "Invalid function output"

    hints = []

    long =
        "Explanation: A function can return an output “term” that has a given “type”,    \n\
        \like this:                                                                      \n\
        \                                                                                \n\
        \                                                                                \n\
        \    ┌────────────────────┐                                                      \n\
        \    │ ∀(x : Text) → Bool │  This is the type of a function that returns an      \n\
        \    └────────────────────┘  output term that has type ❰Bool❱                    \n\
        \                    ⇧                                                           \n\
        \                    This is the type of the output term                         \n\
        \                                                                                \n\
        \                                                                                \n\
        \    ┌────────────────┐                                                          \n\
        \    │ Bool → Natural │  This is the type of a function that returns an output   \n\
        \    └────────────────┘  term that has type ❰Natural❱                            \n\
        \             ⇧                                                                  \n\
        \             This is the type of the output term                                \n\
        \                                                                                \n\
        \                                                                                \n\
        \... or a function can return an output “type” that has a given “kind”, like     \n\
        \this:                                                                           \n\
        \                                                                                \n\
        \    ┌────────────────────┐                                                      \n\
        \    │ ∀(a : Type) → Type │  This is the type of a function that returns an      \n\
        \    └────────────────────┘  output type that has kind ❰Type❱                    \n\
        \                    ⇧                                                           \n\
        \                    This is the kind of the output type                         \n\
        \                                                                                \n\
        \                                                                                \n\
        \    ┌──────────────────────┐                                                    \n\
        \    │ (Type → Type) → Type │  This is the type of a function that returns an    \n\
        \    └──────────────────────┘  output type that has kind ❰Type❱                  \n\
        \                      ⇧                                                         \n\
        \                      This is the kind of the output type                       \n\
        \                                                                                \n\
        \                                                                                \n\
        \Other outputs are " <> _NOT <> " valid, like this:                              \n\
        \                                                                                \n\
        \                                                                                \n\
        \    ┌─────────────────┐                                                         \n\
        \    │ ∀(x : Bool) → x │  ❰x❱ is a “term” and not a “type” nor a “kind” so the   \n\
        \    └─────────────────┘  output cannot have “type” ❰x❱ or “kind” ❰x❱            \n\
        \                    ⇧                                                           \n\
        \                    This is not a type or kind                                  \n\
        \                                                                                \n\
        \                                                                                \n\
        \    ┌─────────────┐                                                             \n\
        \    │ Text → True │  ❰True❱ is a “term” and not a “type” nor a “kind” so the    \n\
        \    └─────────────┘  output cannot have “type” ❰True❱ or “kind” ❰True❱          \n\
        \             ⇧                                                                  \n\
        \             This is not a type or kind                                         \n\
        \                                                                                \n\
        \                                                                                \n\
        \Some common reasons why you might get this error:                               \n\
        \                                                                                \n\
        \● You use ❰∀❱ instead of ❰λ❱ by mistake, like this:                             \n\
        \                                                                                \n\
        \                                                                                \n\
        \    ┌────────────────┐                                                          \n\
        \    │ ∀(x: Bool) → x │                                                          \n\
        \    └────────────────┘                                                          \n\
        \      ⇧                                                                         \n\
        \      Using ❰λ❱ here instead of ❰∀❱ would transform this into a valid function  \n\
        \                                                                                \n\
        \                                                                                \n\
        \────────────────────────────────────────────────────────────────────────────────\n\
        \                                                                                \n\
        \You specified that your function outputs a:                                     \n\
        \                                                                                \n\
        \" <> txt <> "\n\
        \                                                                                \n\
        \... which is neither a type nor a kind:                                         \n"
      where
        txt = insert expr

prettyTypeMessage (NotAFunction expr0 expr1) = ErrorMessages {..}
  where
    short = "Not a function"

    hints = []

    long =
        "Explanation: Expressions separated by whitespace denote function application,   \n\
        \like this:                                                                      \n\
        \                                                                                \n\
        \                                                                                \n\
        \    ┌─────┐                                                                     \n\
        \    │ f x │  This denotes the function ❰f❱ applied to an argument named ❰x❱     \n\
        \    └─────┘                                                                     \n\
        \                                                                                \n\
        \                                                                                \n\
        \A function is a term that has type ❰a → b❱ for some ❰a❱ or ❰b❱.  For example,   \n\
        \the following expressions are all functions because they have a function type:  \n\
        \                                                                                \n\
        \                                                                                \n\
        \                        The function's input type is ❰Bool❱                     \n\
        \                        ⇩                                                       \n\
        \    ┌───────────────────────────────┐                                           \n\
        \    │ λ(x : Bool) → x : Bool → Bool │  User-defined anonymous function          \n\
        \    └───────────────────────────────┘                                           \n\
        \                               ⇧                                                \n\
        \                               The function's output type is ❰Bool❱             \n\
        \                                                                                \n\
        \                                                                                \n\
        \                     The function's input type is ❰Natural❱                     \n\
        \                     ⇩                                                          \n\
        \    ┌───────────────────────────────┐                                           \n\
        \    │ Natural/even : Natural → Bool │  Built-in function                        \n\
        \    └───────────────────────────────┘                                           \n\
        \                               ⇧                                                \n\
        \                               The function's output type is ❰Bool❱             \n\
        \                                                                                \n\
        \                                                                                \n\
        \                        The function's input kind is ❰Type❱                     \n\
        \                        ⇩                                                       \n\
        \    ┌───────────────────────────────┐                                           \n\
        \    │ λ(a : Type) → a : Type → Type │  Type-level functions are still functions \n\
        \    └───────────────────────────────┘                                           \n\
        \                               ⇧                                                \n\
        \                               The function's output kind is ❰Type❱             \n\
        \                                                                                \n\
        \                                                                                \n\
        \             The function's input kind is ❰Type❱                                \n\
        \             ⇩                                                                  \n\
        \    ┌────────────────────┐                                                      \n\
        \    │ List : Type → Type │  Built-in type-level function                        \n\
        \    └────────────────────┘                                                      \n\
        \                    ⇧                                                           \n\
        \                    The function's output kind is ❰Type❱                        \n\
        \                                                                                \n\
        \                                                                                \n\
        \                        Function's input has kind ❰Type❱                        \n\
        \                        ⇩                                                       \n\
        \    ┌─────────────────────────────────────────────────┐                         \n\
        \    │ List/head : ∀(a : Type) → (List a → Optional a) │  A function can return  \n\
        \    └─────────────────────────────────────────────────┘  another function       \n\
        \                                ⇧                                               \n\
        \                                Function's output has type ❰List a → Optional a❱\n\
        \                                                                                \n\
        \                                                                                \n\
        \                       The function's input type is ❰List Text❱                 \n\
        \                       ⇩                                                        \n\
        \    ┌────────────────────────────────────────────┐                              \n\
        \    │ List/head Text : List Text → Optional Text │  A function applied to an    \n\
        \    └────────────────────────────────────────────┘  argument can be a function  \n\
        \                                   ⇧                                            \n\
        \                                   The function's output type is ❰Optional Text❱\n\
        \                                                                                \n\
        \                                                                                \n\
        \An expression is not a function if the expression's type is not of the form     \n\
        \❰a → b❱.  For example, these are " <> _NOT <> " functions:                      \n\
        \                                                                                \n\
        \                                                                                \n\
        \    ┌─────────────┐                                                             \n\
        \    │ 1 : Natural │  ❰1❱ is not a function because ❰Natural❱ is not the type of \n\
        \    └─────────────┘  a function                                                 \n\
        \                                                                                \n\
        \                                                                                \n\
        \    ┌───────────────────────┐                                                   \n\
        \    │ Natural/even 2 : Bool │  ❰Natural/even 2❱ is not a function because       \n\
        \    └───────────────────────┘  ❰Bool❱ is not the type of a function             \n\
        \                                                                                \n\
        \                                                                                \n\
        \    ┌──────────────────┐                                                        \n\
        \    │ List Text : Type │  ❰List Text❱ is not a function because ❰Type❱ is not   \n\
        \    └──────────────────┘  the type of a function                                \n\
        \                                                                                \n\
        \                                                                                \n\
        \Some common reasons why you might get this error:                               \n\
        \                                                                                \n\
        \● You tried to add two ❰Natural❱s without a space around the ❰+❱, like this:    \n\
        \                                                                                \n\
        \                                                                                \n\
        \    ┌─────┐                                                                     \n\
        \    │ 2+2 │                                                                     \n\
        \    └─────┘                                                                     \n\
        \                                                                                \n\
        \                                                                                \n\
        \  The above code is parsed as:                                                  \n\
        \                                                                                \n\
        \                                                                                \n\
        \    ┌────────┐                                                                  \n\
        \    │ 2 (+2) │                                                                  \n\
        \    └────────┘                                                                  \n\
        \      ⇧                                                                         \n\
        \      The compiler thinks that this ❰2❱ is a function whose argument is ❰+2❱    \n\
        \                                                                                \n\
        \                                                                                \n\
        \  This is because the ❰+❱ symbol has two meanings: you use ❰+❱ to add two       \n\
        \  numbers, but you also can prefix ❰Natural❱ literals with a ❰+❱ to turn them   \n\
        \  into ❰Integer❱ literals (like ❰+2❱)                                           \n\
        \                                                                                \n\
        \  To fix the code, you need to put spaces around the ❰+❱, like this:            \n\
        \                                                                                \n\
        \                                                                                \n\
        \    ┌───────┐                                                                   \n\
        \    │ 2 + 2 │                                                                   \n\
        \    └───────┘                                                                   \n\
        \                                                                                \n\
        \                                                                                \n\
        \────────────────────────────────────────────────────────────────────────────────\n\
        \                                                                                \n\
        \You tried to use the following expression as a function:                        \n\
        \                                                                                \n\
        \" <> txt0 <> "\n\
        \                                                                                \n\
        \... but this expression's type is:                                              \n\
        \                                                                                \n\
        \" <> txt1 <> "\n\
        \                                                                                \n\
        \... which is not a function type                                                \n"
      where
        txt0 = insert expr0
        txt1 = insert expr1

prettyTypeMessage (TypeMismatch expr0 expr1 expr2 expr3) = ErrorMessages {..}
  where
    short = "Wrong type of function argument\n"
        <>  "\n"
        <>  Dhall.Diff.doc (Dhall.Diff.diffNormalized expr1 expr3)

    hints = emptyRecordTypeHint expr2

    long =
        "Explanation: Every function declares what type or kind of argument to accept    \n\
        \                                                                                \n\
        \For example:                                                                    \n\
        \                                                                                \n\
        \                                                                                \n\
        \    ┌───────────────────────────────┐                                           \n\
        \    │ λ(x : Bool) → x : Bool → Bool │  This anonymous function only accepts     \n\
        \    └───────────────────────────────┘  arguments that have type ❰Bool❱          \n\
        \                        ⇧                                                       \n\
        \                        The function's input type                               \n\
        \                                                                                \n\
        \                                                                                \n\
        \    ┌───────────────────────────────┐                                           \n\
        \    │ Natural/even : Natural → Bool │  This built-in function only accepts      \n\
        \    └───────────────────────────────┘  arguments that have type ❰Natural❱       \n\
        \                     ⇧                                                          \n\
        \                     The function's input type                                  \n\
        \                                                                                \n\
        \                                                                                \n\
        \    ┌───────────────────────────────┐                                           \n\
        \    │ λ(a : Type) → a : Type → Type │  This anonymous function only accepts     \n\
        \    └───────────────────────────────┘  arguments that have kind ❰Type❱          \n\
        \                        ⇧                                                       \n\
        \                        The function's input kind                               \n\
        \                                                                                \n\
        \                                                                                \n\
        \    ┌────────────────────┐                                                      \n\
        \    │ List : Type → Type │  This built-in function only accepts arguments that  \n\
        \    └────────────────────┘  have kind ❰Type❱                                    \n\
        \             ⇧                                                                  \n\
        \             The function's input kind                                          \n\
        \                                                                                \n\
        \                                                                                \n\
        \For example, the following expressions are valid:                               \n\
        \                                                                                \n\
        \                                                                                \n\
        \    ┌────────────────────────┐                                                  \n\
        \    │ (λ(x : Bool) → x) True │  ❰True❱ has type ❰Bool❱, which matches the type  \n\
        \    └────────────────────────┘  of argument that the anonymous function accepts \n\
        \                                                                                \n\
        \                                                                                \n\
        \    ┌────────────────┐                                                          \n\
        \    │ Natural/even 2 │  ❰2❱ has type ❰Natural❱, which matches the type of       \n\
        \    └────────────────┘  argument that the ❰Natural/even❱ function accepts,      \n\
        \                                                                                \n\
        \                                                                                \n\
        \    ┌────────────────────────┐                                                  \n\
        \    │ (λ(a : Type) → a) Bool │  ❰Bool❱ has kind ❰Type❱, which matches the kind  \n\
        \    └────────────────────────┘  of argument that the anonymous function accepts \n\
        \                                                                                \n\
        \                                                                                \n\
        \    ┌───────────┐                                                               \n\
        \    │ List Text │  ❰Text❱ has kind ❰Type❱, which matches the kind of argument   \n\
        \    └───────────┘  that that the ❰List❱ function accepts                        \n\
        \                                                                                \n\
        \                                                                                \n\
        \However, you can " <> _NOT <> " apply a function to the wrong type or kind of argument\n\
        \                                                                                \n\
        \For example, the following expressions are not valid:                           \n\
        \                                                                                \n\
        \                                                                                \n\
        \    ┌───────────────────────┐                                                   \n\
        \    │ (λ(x : Bool) → x) \"A\" │  ❰\"A\"❱ has type ❰Text❱, but the anonymous function\n\
        \    └───────────────────────┘  expects an argument that has type ❰Bool❱         \n\
        \                                                                                \n\
        \                                                                                \n\
        \    ┌──────────────────┐                                                        \n\
        \    │ Natural/even \"A\" │  ❰\"A\"❱ has type ❰Text❱, but the ❰Natural/even❱ function\n\
        \    └──────────────────┘  expects an argument that has type ❰Natural❱           \n\
        \                                                                                \n\
        \                                                                                \n\
        \    ┌────────────────────────┐                                                  \n\
        \    │ (λ(a : Type) → a) True │  ❰True❱ has type ❰Bool❱, but the anonymous       \n\
        \    └────────────────────────┘  function expects an argument of kind ❰Type❱     \n\
        \                                                                                \n\
        \                                                                                \n\
        \    ┌────────┐                                                                  \n\
        \    │ List 1 │  ❰1❱ has type ❰Natural❱, but the ❰List❱ function expects an      \n\
        \    └────────┘  argument that has kind ❰Type❱                                   \n\
        \                                                                                \n\
        \                                                                                \n\
        \Some common reasons why you might get this error:                               \n\
        \                                                                                \n\
        \● You omit a function argument by mistake:                                      \n\
        \                                                                                \n\
        \                                                                                \n\
        \    ┌───────────────────────┐                                                   \n\
        \    │ List/head   [1, 2, 3] │                                                   \n\
        \    └───────────────────────┘                                                   \n\
        \                ⇧                                                               \n\
        \                ❰List/head❱ is missing the first argument,                      \n\
        \                which should be: ❰Natural❱                                      \n\
        \                                                                                \n\
        \                                                                                \n\
        \● You supply an ❰Integer❱ literal to a function that expects a ❰Natural❱        \n\
        \                                                                                \n\
        \                                                                                \n\
        \    ┌─────────────────┐                                                         \n\
        \    │ Natural/even +2 │                                                         \n\
        \    └─────────────────┘                                                         \n\
        \                   ⇧                                                            \n\
        \                   This should be ❰2❱                                           \n\
        \                                                                                \n\
        \                                                                                \n\
        \────────────────────────────────────────────────────────────────────────────────\n\
        \                                                                                \n\
        \You tried to invoke the following function:                                     \n\
        \                                                                                \n\
        \" <> txt0 <> "\n\
        \                                                                                \n\
        \... which expects an argument of type or kind:                                  \n\
        \                                                                                \n\
        \" <> txt1 <> "\n\
        \                                                                                \n\
        \... on the following argument:                                                  \n\
        \                                                                                \n\
        \" <> txt2 <> "\n\
        \                                                                                \n\
        \... which has a different type or kind:                                         \n\
        \                                                                                \n\
        \" <> txt3 <> "\n"
      where
        txt0 = insert expr0
        txt1 = insert expr1
        txt2 = insert expr2
        txt3 = insert expr3

prettyTypeMessage (AnnotMismatch expr0 expr1 expr2) = ErrorMessages {..}
  where
    short = "Expression doesn't match annotation\n"
        <>  "\n"
        <>  Dhall.Diff.doc (Dhall.Diff.diffNormalized expr1 expr2)

    hints = []

    long =
        "Explanation: You can annotate an expression with its type or kind using the     \n\
        \❰:❱ symbol, like this:                                                          \n\
        \                                                                                \n\
        \                                                                                \n\
        \    ┌───────┐                                                                   \n\
        \    │ x : t │  ❰x❱ is an expression and ❰t❱ is the annotated type or kind of ❰x❱\n\
        \    └───────┘                                                                   \n\
        \                                                                                \n\
        \The type checker verifies that the expression's type or kind matches the        \n\
        \provided annotation                                                             \n\
        \                                                                                \n\
        \For example, all of the following are valid annotations that the type checker   \n\
        \accepts:                                                                        \n\
        \                                                                                \n\
        \                                                                                \n\
        \    ┌─────────────┐                                                             \n\
        \    │ 1 : Natural │  ❰1❱ is an expression that has type ❰Natural❱, so the type  \n\
        \    └─────────────┘  checker accepts the annotation                             \n\
        \                                                                                \n\
        \                                                                                \n\
        \    ┌───────────────────────┐                                                   \n\
        \    │ Natural/even 2 : Bool │  ❰Natural/even 2❱ has type ❰Bool❱, so the type    \n\
        \    └───────────────────────┘  checker accepts the annotation                   \n\
        \                                                                                \n\
        \                                                                                \n\
        \    ┌────────────────────┐                                                      \n\
        \    │ List : Type → Type │  ❰List❱ is an expression that has kind ❰Type → Type❱,\n\
        \    └────────────────────┘  so the type checker accepts the annotation          \n\
        \                                                                                \n\
        \                                                                                \n\
        \    ┌──────────────────┐                                                        \n\
        \    │ List Text : Type │  ❰List Text❱ is an expression that has kind ❰Type❱, so \n\
        \    └──────────────────┘  the type checker accepts the annotation               \n\
        \                                                                                \n\
        \                                                                                \n\
        \However, the following annotations are " <> _NOT <> " valid and the type checker will\n\
        \reject them:                                                                    \n\
        \                                                                                \n\
        \                                                                                \n\
        \    ┌──────────┐                                                                \n\
        \    │ 1 : Text │  The type checker rejects this because ❰1❱ does not have type  \n\
        \    └──────────┘  ❰Text❱                                                        \n\
        \                                                                                \n\
        \                                                                                \n\
        \    ┌─────────────┐                                                             \n\
        \    │ List : Type │  ❰List❱ does not have kind ❰Type❱                           \n\
        \    └─────────────┘                                                             \n\
        \                                                                                \n\
        \                                                                                \n\
        \Some common reasons why you might get this error:                               \n\
        \                                                                                \n\
        \● The Haskell Dhall interpreter implicitly inserts a top-level annotation       \n\
        \  matching the expected type                                                    \n\
        \                                                                                \n\
        \  For example, if you run the following Haskell code:                           \n\
        \                                                                                \n\
        \                                                                                \n\
        \    ┌───────────────────────────────┐                                           \n\
        \    │ >>> input auto \"1\" :: IO Text │                                         \n\
        \    └───────────────────────────────┘                                           \n\
        \                                                                                \n\
        \                                                                                \n\
        \  ... then the interpreter will actually type check the following annotated     \n\
        \  expression:                                                                   \n\
        \                                                                                \n\
        \                                                                                \n\
        \    ┌──────────┐                                                                \n\
        \    │ 1 : Text │                                                                \n\
        \    └──────────┘                                                                \n\
        \                                                                                \n\
        \                                                                                \n\
        \  ... and then type-checking will fail                                          \n\
        \                                                                                \n\
        \────────────────────────────────────────────────────────────────────────────────\n\
        \                                                                                \n\
        \You or the interpreter annotated this expression:                               \n\
        \                                                                                \n\
        \" <> txt0 <> "\n\
        \                                                                                \n\
        \... with this type or kind:                                                     \n\
        \                                                                                \n\
        \" <> txt1 <> "\n\
        \                                                                                \n\
        \... but the inferred type or kind of the expression is actually:                \n\
        \                                                                                \n\
        \" <> txt2 <> "\n"
      where
        txt0 = insert expr0
        txt1 = insert expr1
        txt2 = insert expr2

prettyTypeMessage Untyped = ErrorMessages {..}
  where
    short = "❰Sort❱ has no type, kind, or sort"

    hints = []

    long =
        "Explanation: There are five levels of expressions that form a hierarchy:        \n\
        \                                                                                \n\
        \● terms                                                                         \n\
        \● types                                                                         \n\
        \● kinds                                                                         \n\
        \● sorts                                                                         \n\
        \● orders                                                                        \n\
        \                                                                                \n\
        \The following example illustrates this hierarchy:                               \n\
        \                                                                                \n\
        \    ┌───────────────────────────────────┐                                       \n\
        \    │ \"ABC\" : Text : Type : Kind : Sort │                                     \n\
        \    └───────────────────────────────────┘                                       \n\
        \       ⇧      ⇧      ⇧      ⇧      ⇧                                            \n\
        \       term   type   kind   sort   order                                        \n\
        \                                                                                \n\
        \There is nothing above ❰Sort❱ in this hierarchy, so if you try to type check any\n\
        \expression containing ❰Sort❱ anywhere in the expression then type checking fails\n\
        \                                                                                \n\
        \Some common reasons why you might get this error:                               \n\
        \                                                                                \n\
        \● You supplied a sort where a kind was expected                                 \n\
        \                                                                                \n\
        \  For example, the following expression will fail to type check:                \n\
        \                                                                                \n\
        \    ┌──────────────────┐                                                        \n\
        \    │ f : Type -> Kind │                                                        \n\
        \    └──────────────────┘                                                        \n\
        \                  ⇧                                                             \n\
        \                  ❰Kind❱ is a sort, not a kind                                  \n"

prettyTypeMessage (InvalidPredicate expr0 expr1) = ErrorMessages {..}
  where
    short = "Invalid predicate for ❰if❱: "
        <>  "\n"
        <>  Dhall.Diff.doc (Dhall.Diff.diffNormalized Bool expr1)

    hints = []

    long =
        "Explanation: Every ❰if❱ expression begins with a predicate which must have type \n\
        \❰Bool❱                                                                          \n\
        \                                                                                \n\
        \For example, these are valid ❰if❱ expressions:                                  \n\
        \                                                                                \n\
        \                                                                                \n\
        \    ┌──────────────────────────────┐                                            \n\
        \    │ if True then \"Yes\" else \"No\" │                                        \n\
        \    └──────────────────────────────┘                                            \n\
        \         ⇧                                                                      \n\
        \         Predicate                                                              \n\
        \                                                                                \n\
        \                                                                                \n\
        \    ┌─────────────────────────────────────────┐                                 \n\
        \    │ λ(x : Bool) → if x then False else True │                                 \n\
        \    └─────────────────────────────────────────┘                                 \n\
        \                       ⇧                                                        \n\
        \                       Predicate                                                \n\
        \                                                                                \n\
        \                                                                                \n\
        \... but these are " <> _NOT <> " valid ❰if❱ expressions:                        \n\
        \                                                                                \n\
        \                                                                                \n\
        \    ┌───────────────────────────┐                                               \n\
        \    │ if 0 then \"Yes\" else \"No\" │  ❰0❱ does not have type ❰Bool❱            \n\
        \    └───────────────────────────┘                                               \n\
        \                                                                                \n\
        \                                                                                \n\
        \    ┌────────────────────────────┐                                              \n\
        \    │ if \"\" then False else True │  ❰\"\"❱ does not have type ❰Bool❱          \n\
        \    └────────────────────────────┘                                              \n\
        \                                                                                \n\
        \                                                                                \n\
        \Some common reasons why you might get this error:                               \n\
        \                                                                                \n\
        \● You might be used to other programming languages that accept predicates other \n\
        \  than ❰Bool❱                                                                   \n\
        \                                                                                \n\
        \  For example, some languages permit ❰0❱ or ❰\"\"❱ as valid predicates and treat\n\
        \  them as equivalent to ❰False❱.  However, the Dhall language does not permit   \n\
        \  this                                                                          \n\
        \                                                                                \n\
        \────────────────────────────────────────────────────────────────────────────────\n\
        \                                                                                \n\
        \Your ❰if❱ expression begins with the following predicate:                       \n\
        \                                                                                \n\
        \" <> txt0 <> "\n\
        \                                                                                \n\
        \... that has type:                                                              \n\
        \                                                                                \n\
        \" <> txt1 <> "\n\
        \                                                                                \n\
        \... but the predicate must instead have type ❰Bool❱                             \n"
      where
        txt0 = insert expr0
        txt1 = insert expr1

prettyTypeMessage (IfBranchMismatch expr0 expr1 expr2 expr3) =
    ErrorMessages {..}
  where
    short = "❰if❱ branches must have matching types\n"
        <>  "\n"
        <>  Dhall.Diff.doc (Dhall.Diff.diffNormalized expr1 expr3)

    hints = []

    long =
        "Explanation: Every ❰if❱ expression has a ❰then❱ and ❰else❱ branch, each of which\n\
        \is an expression:                                                               \n\
        \                                                                                \n\
        \                                                                                \n\
        \                   Expression for ❰then❱ branch                                 \n\
        \                   ⇩                                                            \n\
        \    ┌────────────────────────────────┐                                          \n\
        \    │ if True then \"Hello, world!\"   │                                        \n\
        \    │         else \"Goodbye, world!\" │                                        \n\
        \    └────────────────────────────────┘                                          \n\
        \                   ⇧                                                            \n\
        \                   Expression for ❰else❱ branch                                 \n\
        \                                                                                \n\
        \                                                                                \n\
        \These two expressions must have the same type.  For example, the following ❰if❱ \n\
        \expressions are all valid:                                                      \n\
        \                                                                                \n\
        \                                                                                \n\
        \    ┌──────────────────────────────────┐                                        \n\
        \    │ λ(b : Bool) → if b then 0 else 1 │ Both branches have type ❰Natural❱      \n\
        \    └──────────────────────────────────┘                                        \n\
        \                                                                                \n\
        \                                                                                \n\
        \    ┌────────────────────────────┐                                              \n\
        \    │ λ(b : Bool) →              │                                              \n\
        \    │     if b then Natural/even │ Both branches have type ❰Natural → Bool❱     \n\
        \    │          else Natural/odd  │                                              \n\
        \    └────────────────────────────┘                                              \n\
        \                                                                                \n\
        \                                                                                \n\
        \However, the following expression is " <> _NOT <> " valid:                      \n\
        \                                                                                \n\
        \                                                                                \n\
        \                   This branch has type ❰Natural❱                               \n\
        \                   ⇩                                                            \n\
        \    ┌────────────────────────┐                                                  \n\
        \    │ if True then 0         │                                                  \n\
        \    │         else \"ABC\"     │                                                \n\
        \    └────────────────────────┘                                                  \n\
        \                   ⇧                                                            \n\
        \                   This branch has type ❰Text❱                                  \n\
        \                                                                                \n\
        \                                                                                \n\
        \The ❰then❱ and ❰else❱ branches must have matching types, even if the predicate  \n\
        \is always ❰True❱ or ❰False❱                                                     \n\
        \                                                                                \n\
        \Your ❰if❱ expression has the following ❰then❱ branch:                           \n\
        \                                                                                \n\
        \" <> txt0 <> "\n\
        \                                                                                \n\
        \... which has type:                                                             \n\
        \                                                                                \n\
        \" <> txt2 <> "\n\
        \                                                                                \n\
        \... and the following ❰else❱ branch:                                            \n\
        \                                                                                \n\
        \" <> txt1 <> "\n\
        \                                                                                \n\
        \... which has a different type:                                                 \n\
        \                                                                                \n\
        \" <> txt3 <> "\n\
        \                                                                                \n\
        \Fix your ❰then❱ and ❰else❱ branches to have matching types                      \n"
      where
        txt0 = insert expr0
        txt1 = insert expr1
        txt2 = insert expr2
        txt3 = insert expr3

prettyTypeMessage (ListLitInvariant) = ErrorMessages {..}
  where
    short = "Internal error: A non-empty list literal violated an internal invariant"

    hints = []

    long =
        "Explanation: Internal error: A non-empty list literal violated an internal      \n\
        \invariant.                                                                      \n\
        \                                                                                \n\
        \A non-empty list literal must always be represented as                          \n\
        \                                                                                \n\
        \    ListLit Nothing [x, y, ...]                                                 \n\
        \                                                                                \n\
        \Please file a bug report at https://github.com/dhall-lang/dhall-haskell/issues, \n\
        \ideally including the offending source code.                                    \n"

prettyTypeMessage (InvalidListType expr0) = ErrorMessages {..}
  where
    short = "Invalid type for ❰List❱"

    hints = []

    long =
        "Explanation: ❰List❱s can optionally document their type with a type annotation, \n\
        \like this:                                                                      \n\
        \                                                                                \n\
        \                                                                                \n\
        \    ┌──────────────────────────┐                                                \n\
        \    │ [1, 2, 3] : List Natural │  A ❰List❱ of three ❰Natural❱ numbers           \n\
        \    └──────────────────────────┘                                                \n\
        \                       ⇧                                                        \n\
        \                       The type of the ❰List❱'s elements, which are ❰Natural❱   \n\
        \                       numbers                                                  \n\
        \                                                                                \n\
        \                                                                                \n\
        \    ┌───────────────────┐                                                       \n\
        \    │ [] : List Natural │  An empty ❰List❱                                      \n\
        \    └───────────────────┘                                                       \n\
        \           ⇧                                                                    \n\
        \           You must specify the type when the ❰List❱ is empty                   \n\
        \                                                                                \n\
        \                                                                                \n\
        \The type must be of the form ❰List ...❱ and not something else.  For example,   \n\
        \the following type annotation is " <> _NOT <> " valid:                          \n\
        \                                                                                \n\
        \                                                                                \n\
        \    ┌────────────┐                                                              \n\
        \    │ ... : Bool │                                                              \n\
        \    └────────────┘                                                              \n\
        \            ⇧                                                                   \n\
        \            This type does not have the form ❰List ...❱                         \n\
        \                                                                                \n\
        \                                                                                \n\
        \The element type must be a type and not something else.  For example, the       \n\
        \following element types are " <> _NOT <> " valid:                               \n\
        \                                                                                \n\
        \                                                                                \n\
        \    ┌──────────────┐                                                            \n\
        \    │ ... : List 1 │                                                            \n\
        \    └──────────────┘                                                            \n\
        \                 ⇧                                                              \n\
        \                 This is a ❰Natural❱ number and not a ❰Type❱                    \n\
        \                                                                                \n\
        \                                                                                \n\
        \    ┌─────────────────┐                                                         \n\
        \    │ ... : List Type │                                                         \n\
        \    └─────────────────┘                                                         \n\
        \                 ⇧                                                              \n\
        \                 This is a ❰Kind❱ and not a ❰Type❱                              \n\
        \                                                                                \n\
        \                                                                                \n\
        \You declared that the ❰List❱ should have type:                                  \n\
        \                                                                                \n\
        \" <> txt0 <> "\n\
        \                                                                                \n\
        \... which is not a valid list type                                              \n"
      where
        txt0 = insert expr0

prettyTypeMessage MissingListType =
    ErrorMessages {..}
  where
    short = "An empty list requires a type annotation"

    hints = []

    long =
        "Explanation: Lists do not require a type annotation if they have at least one   \n\
        \element:                                                                        \n\
        \                                                                                \n\
        \                                                                                \n\
        \    ┌───────────┐                                                               \n\
        \    │ [1, 2, 3] │  The compiler can infer that this list has type ❰List Natural❱\n\
        \    └───────────┘                                                               \n\
        \                                                                                \n\
        \                                                                                \n\
        \However, empty lists still require a type annotation:                           \n\
        \                                                                                \n\
        \                                                                                \n\
        \    ┌───────────────────┐                                                       \n\
        \    │ [] : List Natural │  This type annotation is mandatory                    \n\
        \    └───────────────────┘                                                       \n\
        \                                                                                \n\
        \                                                                                \n\
        \You cannot supply an empty list without a type annotation                       \n"

prettyTypeMessage (MismatchedListElements i expr0 _expr1 expr2) =
    ErrorMessages {..}
  where
    short = "List elements should all have the same type\n"
        <>  "\n"
        <>  Dhall.Diff.doc (Dhall.Diff.diffNormalized expr0 expr2)

    hints = []

    long =
        "Explanation: Every element in a list must have the same type                    \n\
        \                                                                                \n\
        \For example, this is a valid ❰List❱:                                            \n\
        \                                                                                \n\
        \                                                                                \n\
        \    ┌───────────┐                                                               \n\
        \    │ [1, 2, 3] │  Every element in this ❰List❱ is a ❰Natural❱ number           \n\
        \    └───────────┘                                                               \n\
        \                                                                                \n\
        \                                                                                \n\
        \.. but this is " <> _NOT <> " a valid ❰List❱:                                   \n\
        \                                                                                \n\
        \                                                                                \n\
        \    ┌───────────────┐                                                           \n\
        \    │ [1, \"ABC\", 3] │  The first and second element have different types      \n\
        \    └───────────────┘                                                           \n\
        \                                                                                \n\
        \                                                                                \n\
        \Your first ❰List❱ element has this type:                                        \n\
        \                                                                                \n\
        \" <> txt0 <> "\n\
        \                                                                                \n\
        \... but the element at index #" <> txt1 <> " has this type instead:             \n\
        \                                                                                \n\
        \" <> txt3 <> "\n"
      where
        txt0 = insert expr0
        txt1 = pretty i
        txt3 = insert expr2

prettyTypeMessage (InvalidListElement i expr0 _expr1 expr2) =
    ErrorMessages {..}
  where
    short = "List element has the wrong type\n"
        <>  "\n"
        <>  Dhall.Diff.doc (Dhall.Diff.diffNormalized expr0 expr2)

    hints = []

    long =
        "Explanation: Every element in the list must have a type matching the type       \n\
        \annotation at the end of the list                                               \n\
        \                                                                                \n\
        \For example, this is a valid ❰List❱:                                            \n\
        \                                                                                \n\
        \                                                                                \n\
        \    ┌──────────────────────────┐                                                \n\
        \    │ [1, 2, 3] : List Natural │  Every element in this ❰List❱ is an ❰Natural❱  \n\
        \    └──────────────────────────┘                                                \n\
        \                                                                                \n\
        \                                                                                \n\
        \.. but this is " <> _NOT <> " a valid ❰List❱:                                   \n\
        \                                                                                \n\
        \                                                                                \n\
        \    ┌──────────────────────────────┐                                            \n\
        \    │ [1, \"ABC\", 3] : List Natural │  The second element is not an ❰Natural❱  \n\
        \    └──────────────────────────────┘                                            \n\
        \                                                                                \n\
        \                                                                                \n\
        \Your ❰List❱ elements should have this type:                                     \n\
        \                                                                                \n\
        \" <> txt0 <> "\n\
        \                                                                                \n\
        \... but the element at index #" <> txt1 <> " has this type instead:             \n\
        \                                                                                \n\
        \" <> txt3 <> "\n"
      where
        txt0 = insert expr0
        txt1 = pretty i
        txt3 = insert expr2

prettyTypeMessage (InvalidSome expr0 expr1 expr2) = ErrorMessages {..}
  where
    short = "❰Some❱ argument has the wrong type"

    hints = []

    long =
        "Explanation: The ❰Some❱ constructor expects an argument that is a term, where   \n\
        \the type of the type of a term must be ❰Type❱                                   \n\
        \                                                                                \n\
        \For example, this is a valid use of ❰Some❱:                                     \n\
        \                                                                                \n\
        \                                                                                \n\
        \    ┌────────┐                                                                  \n\
        \    │ Some 1 │  ❰1❱ is a valid term because ❰1 : Natural : Type❱                \n\
        \    └────────┘                                                                  \n\
        \                                                                                \n\
        \                                                                                \n\
        \... but this is " <> _NOT <> " a valid ❰Optional❱ value:                        \n\
        \                                                                                \n\
        \                                                                                \n\
        \    ┌───────────┐                                                               \n\
        \    │ Some Text │  ❰Text❱ is not a valid term because ❰Text : Type : Kind ❱     \n\
        \    └───────────┘                                                               \n\
        \                                                                                \n\
        \                                                                                \n\
        \The ❰Some❱ argument you provided:                                               \n\
        \                                                                                \n\
        \" <> txt0 <> "\n\
        \                                                                                \n\
        \... has this type:                                                              \n\
        \                                                                                \n\
        \" <> txt1 <> "\n\
        \                                                                                \n\
        \... but the type of that type is:                                               \n\
        \                                                                                \n\
        \" <> txt2 <> "\n\
        \                                                                                \n\
        \... which is not ❰Type❱                                                         \n"
      where
        txt0 = insert expr0
        txt1 = insert expr1
        txt2 = insert expr2

prettyTypeMessage (InvalidFieldType k expr0) = ErrorMessages {..}
  where
    short = "Invalid field type"

    hints = []

    long =
        "Explanation: Every record type annotates each field with a ❰Type❱, a ❰Kind❱, or \n\
        \a ❰Sort❱ like this:                                                             \n\
        \                                                                                \n\
        \                                                                                \n\
        \    ┌──────────────────────────────────────────────┐                            \n\
        \    │ { foo : Natural, bar : Integer, baz : Text } │  Every field is annotated  \n\
        \    └──────────────────────────────────────────────┘  with a ❰Type❱             \n\
        \                                                                                \n\
        \                                                                                \n\
        \    ┌────────────────────────────┐                                              \n\
        \    │ { foo : Type, bar : Type } │  Every field is annotated                    \n\
        \    └────────────────────────────┘  with a ❰Kind❱                               \n\
        \                                                                                \n\
        \                                                                                \n\
        \However, the types of fields may " <> _NOT <> " be term-level values:           \n\
        \                                                                                \n\
        \                                                                                \n\
        \    ┌────────────────────────────┐                                              \n\
        \    │ { foo : Natural, bar : 1 } │  Invalid record type                         \n\
        \    └────────────────────────────┘                                              \n\
        \                             ⇧                                                  \n\
        \                             ❰1❱ is a ❰Natural❱ number and not a ❰Type❱,        \n\
        \                             ❰Kind❱, or ❰Sort❱                                  \n\
        \                                                                                \n\
        \                                                                                \n\
        \You provided a record type with a field named:                                  \n\
        \                                                                                \n\
        \" <> txt0 <> "\n\
        \                                                                                \n\
        \... annotated with the following expression:                                    \n\
        \                                                                                \n\
        \" <> txt1 <> "\n\
        \                                                                                \n\
        \... which is neither a ❰Type❱, a ❰Kind❱, nor a ❰Sort❱                           \n"
      where
        txt0 = insert k
        txt1 = insert expr0

prettyTypeMessage (InvalidAlternativeType k expr0) = ErrorMessages {..}
  where
    short = "Invalid alternative type"

    hints = []

    long =
        "Explanation: Every union type specifies the type of each alternative, like this:\n\
        \                                                                                \n\
        \                                                                                \n\
        \               The type of the first alternative is ❰Bool❱                      \n\
        \               ⇩                                                                \n\
        \    ┌──────────────────────────────────┐                                        \n\
        \    │ < Left : Bool, Right : Natural > │  A union type with two alternatives    \n\
        \    └──────────────────────────────────┘                                        \n\
        \                             ⇧                                                  \n\
        \                             The type of the second alternative is ❰Natural❱    \n\
        \                                                                                \n\
        \                                                                                \n\
        \However, these alternatives can only be annotated with ❰Type❱s, ❰Kind❱s, or     \n\
        \❰Sort❱s.  For example, the following union types are " <> _NOT <> " valid:      \n\
        \                                                                                \n\
        \                                                                                \n\
        \    ┌────────────────────────────┐                                              \n\
        \    │ < Left : Bool, Right : 1 > │  Invalid union type                          \n\
        \    └────────────────────────────┘                                              \n\
        \                             ⇧                                                  \n\
        \                             This is a ❰Natural❱ and not a ❰Type❱, ❰Kind❱, or   \n\
        \                             ❰Sort❱                                             \n\
        \                                                                                \n\
        \                                                                                \n\
        \Some common reasons why you might get this error:                               \n\
        \                                                                                \n\
        \● You accidentally typed ❰:❱ instead of ❰=❱ for a union literal with one        \n\
        \  alternative:                                                                  \n\
        \                                                                                \n\
        \    ┌─────────────────┐                                                         \n\
        \    │ < Example : 1 > │                                                         \n\
        \    └─────────────────┘                                                         \n\
        \                ⇧                                                               \n\
        \                This could be ❰=❱ instead                                       \n\
        \                                                                                \n\
        \                                                                                \n\
        \────────────────────────────────────────────────────────────────────────────────\n\
        \                                                                                \n\
        \You provided a union type with an alternative named:                            \n\
        \                                                                                \n\
        \" <> txt0 <> "\n\
        \                                                                                \n\
        \... annotated with the following expression which is not a ❰Type❱, ❰Kind❱, or   \n\
        \❰Sort❱:                                                                         \n\
        \                                                                                \n\
        \" <> txt1 <> "\n"
      where
        txt0 = insert k
        txt1 = insert expr0

prettyTypeMessage (ListAppendMismatch expr0 expr1) = ErrorMessages {..}
  where
    short = "You can only append ❰List❱s with matching element types\n"
        <>  "\n"
        <>  Dhall.Diff.doc (Dhall.Diff.diffNormalized expr0 expr1)

    hints = []

    long =
        "Explanation: You can append two ❰List❱s using the ❰#❱ operator, like this:      \n\
        \                                                                                \n\
        \                                                                                \n\
        \    ┌────────────────────┐                                                      \n\
        \    │ [1, 2, 3] # [4, 5] │                                                      \n\
        \    └────────────────────┘                                                      \n\
        \                                                                                \n\
        \                                                                                \n\
        \... but you cannot append two ❰List❱s if they have different element types.     \n\
        \For example, the following expression is " <> _NOT <> " valid:                  \n\
        \                                                                                \n\
        \                                                                                \n\
        \       These elements have type ❰Natural❱                                       \n\
        \       ⇩                                                                        \n\
        \    ┌───────────────────────────┐                                               \n\
        \    │ [1, 2, 3] # [True, False] │  Invalid: the element types don't match       \n\
        \    └───────────────────────────┘                                               \n\
        \                  ⇧                                                             \n\
        \                  These elements have type ❰Bool❱                               \n\
        \                                                                                \n\
        \                                                                                \n\
        \────────────────────────────────────────────────────────────────────────────────\n\
        \                                                                                \n\
        \You tried to append a ❰List❱ thas has elements of type:                         \n\
        \                                                                                \n\
        \" <> txt0 <> "\n\
        \                                                                                \n\
        \... with another ❰List❱ that has elements of type:                              \n\
        \                                                                                \n\
        \" <> txt1 <> "\n\
        \                                                                                \n\
        \... and those two types do not match                                            \n"
      where
        txt0 = insert expr0
        txt1 = insert expr1

prettyTypeMessage (CompletionSchemaMustBeARecord expr0 expr1) = ErrorMessages {..}
  where
    short = "The completion schema must be a record"

    hints = []

    long =
        "Explanation: You can complete records using the ❰::❱ operator:                  \n\
        \                                                                                \n\
        \    ┌─────────────────────────────────────────────────────────────────────────┐ \n\
        \    │ {Type = {foo : Bool, bar : Natural}, default = {bar = 2}::{foo = True}} │ \n\
        \    └─────────────────────────────────────────────────────────────────────────┘ \n\
        \                                                                                \n\
        \... The left-hand side of :: must be a record with 'Type' and 'default' keys    \n\
        \                                                                                \n\
        \You tried to record complete the following value:                               \n\
        \                                                                                \n\
        \" <> txt0 <> "\n\
        \                                                                                \n\
        \... which is not a record. It is:                                               \n\
        \                                                                                \n\
        \" <> txt1 <> "\n"
      where
        txt0 = insert expr0
        txt1 = insert expr1

prettyTypeMessage (InvalidRecordCompletion fieldName expr0) = ErrorMessages {..}
  where
    short = "Completion schema is missing a field: " <> pretty fieldName

    hints = []

    long =
        "Explanation: You can complete records using the ❰::❱ operator like this:\n\
        \                                                                                \n\
        \    ┌─────────────────────────────────────────────────────────────────────────┐ \n\
        \    │ {Type = {foo : Bool, bar : Natural}, default = {bar = 2}::{foo = True}} │ \n\
        \    └─────────────────────────────────────────────────────────────────────────┘ \n\
        \                                                                                \n\
        \... but you need to have both Type and default fields in the completion schema  \n\
        \    (the record on the left of the the ::).                                     \n\
        \                                                                                \n\
        \You tried to do record completion using the schema:                             \n\
        \                                                                                \n\
        \" <> txt0 <> "\n\
        \                                                                                \n\
        \... which is missing the key:                                                   \n\
        \                                                                                \n\
        \" <> txt1 <> "\n"
      where
        txt0 = insert expr0
        txt1 = pretty fieldName

prettyTypeMessage (MustUpdateARecord withExpression expression typeExpression) =
    ErrorMessages {..}
  where
    short = "You can only update records"

    hints = []

    long =
        "Explanation: You can update records using the ❰with❱ keyword, like this:        \n\
        \                                                                                \n\
        \                                                                                \n\
        \    ┌────────────────────────────────┐                                          \n\
        \    │ { x = { y = 1 } } with x.y = 2 │                                          \n\
        \    └────────────────────────────────┘                                          \n\
        \                                                                                \n\
        \                                                                                \n\
        \    ┌────────────────────────────────────────────────────────────┐              \n\
        \    │ λ(r : { foo : { bar : Bool } }) → r with foo.bar = False } │              \n\
        \    └────────────────────────────────────────────────────────────┘              \n\
        \                                                                                \n\
        \                                                                                \n\
        \... but you cannot update values that are not records.                          \n\
        \                                                                                \n\
        \For example, the following expression is " <> _NOT <> " valid:                  \n\
        \                                                                                \n\
        \                                                                                \n\
        \    ┌─────────────────┐                                                         \n\
        \    │ 1 with x = True │                                                         \n\
        \    └─────────────────┘                                                         \n\
        \      ⇧                                                                         \n\
        \      Invalid: Not a record                                                     \n\
        \                                                                                \n\
        \                                                                                \n\
        \────────────────────────────────────────────────────────────────────────────────\n\
        \                                                                                \n\
        \The following expression is not permitted:                                      \n\
        \                                                                                \n\
        \" <> insert withExpression' <> "\n\
        \                                                                                \n\
        \... because the left argument to ❰with❱:                                        \n\
        \                                                                                \n\
        \" <> insert expression <> "\n\
        \                                                                                \n\
        \... is not a record, but is actually a:                                         \n\
        \                                                                                \n\
        \" <> insert typeExpression <> "\n"
      where
        withExpression' = case withExpression of
            With record keys value -> With (Dhall.Core.normalize record) keys value
            _                      -> withExpression

prettyTypeMessage (MustCombineARecord c expression typeExpression) =
    ErrorMessages {..}
  where
    action = case c of
        '∧' -> "combine"
        _   -> "override"

    short = "You can only " <> action <> " records"

    hints = emptyRecordTypeHint expression

    long =
        "Explanation: You can " <> action <> " records using the ❰" <> op <> "❱ operator, like this:\n\
        \                                                                                \n\
        \                                                                                \n\
        \    ┌───────────────────────────────────────────┐                               \n\
        \    │ { foo = 1, bar = \"ABC\" } " <> op <> " { baz = True } │                  \n\
        \    └───────────────────────────────────────────┘                               \n\
        \                                                                                \n\
        \                                                                                \n\
        \    ┌─────────────────────────────────────────────┐                             \n\
        \    │ λ(r : { foo : Bool }) → r " <> op <> " { bar = \"ABC\" } │                \n\
        \    └─────────────────────────────────────────────┘                             \n\
        \                                                                                \n\
        \                                                                                \n\
        \... but you cannot " <> action <> " values that are not records.                \n\
        \                                                                                \n\
        \For example, the following expressions are " <> _NOT <> " valid:                \n\
        \                                                                                \n\
        \                                                                                \n\
        \    ┌──────────────────────────────┐                                            \n\
        \    │ { foo = 1, bar = \"ABC\" } " <> op <> " 1 │                               \n\
        \    └──────────────────────────────┘                                            \n\
        \                                 ⇧                                              \n\
        \                                 Invalid: Not a record                          \n\
        \                                                                                \n\
        \                                                                                \n\
        \    ┌───────────────────────────────────────────┐                               \n\
        \    │ { foo = 1, bar = \"ABC\" } " <> op <> " { baz : Bool } │                  \n\
        \    └───────────────────────────────────────────┘                               \n\
        \                                 ⇧                                              \n\
        \                                 Invalid: This is a record type and not a record\n\
        \                                                                                \n\
        \                                                                                \n\
        \    ┌───────────────────────────────────────────┐                               \n\
        \    │ { foo = 1, bar = \"ABC\" } " <> op <> " < baz : Bool > │                  \n\
        \    └───────────────────────────────────────────┘                               \n\
        \                                 ⇧                                              \n\
        \                                 Invalid: This is a union type and not a record \n\
        \                                                                                \n\
        \                                                                                \n\
        \────────────────────────────────────────────────────────────────────────────────\n\
        \                                                                                \n\
        \You supplied this expression as one of the arguments:                           \n\
        \                                                                                \n\
        \" <> insert expression <> "\n\
        \                                                                                \n\
        \... which is not a record, but is actually a:                                   \n\
        \                                                                                \n\
        \" <> insert typeExpression <> "\n"
      where
        op = pretty c

prettyTypeMessage (InvalidDuplicateField k expr0 expr1) =
    ErrorMessages {..}
  where
    short = "Invalid duplicate field: " <> Dhall.Pretty.Internal.prettyLabel k

    hints = []

    long =
        "Explanation: You can specify a field twice if both fields are themselves        \n\
        \records, like this:                                                             \n\
        \                                                                                \n\
        \                                                                                \n\
        \    ┌──────────────────────────────────────────────────────────┐                \n\
        \    │ { ssh = { enable = True }, ssh = { forwardX11 = True } } │                \n\
        \    └──────────────────────────────────────────────────────────┘                \n\
        \                                                                                \n\
        \                                                                                \n\
        \... because the language automatically merges two occurrences of a field using  \n\
        \the ❰∧❱ operator, and the above example is equivalent to:                       \n\
        \                                                                                \n\
        \                                                                                \n\
        \    ┌─────────────────────────────────────────────────────┐                     \n\
        \    │ { ssh = { enable = True } ∧ { forwardX11 = True } } │                     \n\
        \    └─────────────────────────────────────────────────────┘                     \n\
        \                                                                                \n\
        \                                                                                \n\
        \... which is in turn equivalent to:                                             \n\
        \                                                                                \n\
        \                                                                                \n\
        \    ┌────────────────────────────────────────────────┐                          \n\
        \    │ { ssh = { enable = True, forwardX11 = True } } │                          \n\
        \    └────────────────────────────────────────────────┘                          \n\
        \                                                                                \n\
        \                                                                                \n\
        \However, this implies that both fields must be records since the ❰∧❱ operator   \n\
        \cannot merge non-record values.  For example, these expressions are not valid:  \n\
        \                                                                                \n\
        \                                                                                \n\
        \    ┌──────────────────┐                                                        \n\
        \    │ { x = 0, x = 0 } │  Invalid: Neither field is a record                    \n\
        \    └──────────────────┘                                                        \n\
        \                                                                                \n\
        \                                                                                \n\
        \    ┌──────────────────────────┐                                                \n\
        \    │ { x = 0, x = { y = 0 } } │  Invalid: The first ❰x❱ field is not a record  \n\
        \    └──────────────────────────┘                                                \n\
        \                                                                                \n\
        \                                                                                \n\
        \────────────────────────────────────────────────────────────────────────────────\n\
        \                                                                                \n\
        \You specified more than one field named:                                        \n\
        \                                                                                \n\
        \" <> txt0 <> "\n\
        \                                                                                \n\
        \... but one of the fields had this value:                                       \n\
        \                                                                                \n\
        \" <> txt1 <> "\n\
        \                                                                                \n\
        \... with this type:                                                             \n\
        \                                                                                \n\
        \" <> txt2 <> "\n\
        \                                                                                \n\
        \... which is not a record type                                                  \n"
      where
        txt0 = insert (Dhall.Pretty.Internal.escapeLabel True k)
        txt1 = insert expr0
        txt2 = insert expr1

prettyTypeMessage (CombineTypesRequiresRecordType expr0 expr1) =
    ErrorMessages {..}
  where
    short = "❰⩓❱ requires arguments that are record types"

    hints = []

    long =
        "Explanation: You can only use the ❰⩓❱ operator on arguments that are record type\n\
        \literals, like this:                                                            \n\
        \                                                                                \n\
        \                                                                                \n\
        \    ┌─────────────────────────────────────┐                                     \n\
        \    │ { age : Natural } ⩓ { name : Text } │                                     \n\
        \    └─────────────────────────────────────┘                                     \n\
        \                                                                                \n\
        \                                                                                \n\
        \... but you cannot use the ❰⩓❱ operator on any other type of arguments.  For    \n\
        \example, you cannot use variable arguments:                                     \n\
        \                                                                                \n\
        \                                                                                \n\
        \    ┌───────────────────────────────────┐                                       \n\
        \    │ λ(t : Type) → t ⩓ { name : Text } │  Invalid: ❰t❱ might not be a record   \n\
        \    └───────────────────────────────────┘  type                                 \n\
        \                                                                                \n\
        \                                                                                \n\
        \────────────────────────────────────────────────────────────────────────────────\n\
        \                                                                                \n\
        \You tried to supply the following argument:                                     \n\
        \                                                                                \n\
        \" <> txt0 <> "\n\
        \                                                                                \n\
        \... which normalized to:                                                        \n\
        \                                                                                \n\
        \" <> txt1 <> "\n\
        \                                                                                \n\
        \... which is not a record type literal                                          \n"
      where
        txt0 = insert expr0
        txt1 = insert expr1

prettyTypeMessage (RecordTypeMismatch const0 const1 expr0 expr1) =
    ErrorMessages {..}
  where
    short = "Record type mismatch"

    hints = []

    long =
        "Explanation: You can only use the ❰⩓❱ operator on record types if they are both \n\
        \ ❰Type❱s or ❰Kind❱s:                                                            \n\
        \                                                                                \n\
        \                                                                                \n\
        \    ┌─────────────────────────────────────┐                                     \n\
        \    │ { age : Natural } ⩓ { name : Text } │  Valid: Both arguments are ❰Type❱s  \n\
        \    └─────────────────────────────────────┘                                     \n\
        \                                                                                \n\
        \                                                                                \n\
        \    ┌──────────────────────────────────────┐                                    \n\
        \    │ { Input : Type } ⩓ { Output : Type } │  Valid: Both arguments are ❰Kind❱s \n\
        \    └──────────────────────────────────────┘                                    \n\
        \                                                                                \n\
        \                                                                                \n\
        \... but you cannot combine a ❰Type❱ and a ❰Kind❱:                               \n\
        \                                                                                \n\
        \                                                                                \n\
        \    ┌────────────────────────────────────┐                                      \n\
        \    │ { Input : Type } ⩓ { name : Text } │  Invalid: The arguments do not match \n\
        \    └────────────────────────────────────┘                                      \n\
        \                                                                                \n\
        \                                                                                \n\
        \────────────────────────────────────────────────────────────────────────────────\n\
        \                                                                                \n\
        \You tried to combine the following record type:                                 \n\
        \                                                                                \n\
        \" <> txt0 <> "\n\
        \                                                                                \n\
        \... with this record types:                                                     \n\
        \                                                                                \n\
        \" <> txt1 <> "\n\
        \                                                                                \n\
        \... but the former record type is a:                                            \n\
        \                                                                                \n\
        \" <> txt2 <> "\n\
        \                                                                                \n\
        \... but the latter record type is a:                                            \n\
        \                                                                                \n\
        \" <> txt3 <> "\n"
      where
        txt0 = insert expr0
        txt1 = insert expr1
        txt2 = insert const0
        txt3 = insert const1

prettyTypeMessage (DuplicateFieldCannotBeMerged ks) = ErrorMessages {..}
  where
    short = "Duplicate field cannot be merged: " <> pretty (toPath ks)

    hints = []

    long =
        "Explanation: Duplicate fields are only allowed if they are both records and if  \n\
        \the two records can be recursively merged without collisions.                   \n\
        \                                                                                \n\
        \Specifically, an expression like:                                               \n\
        \                                                                                \n\
        \                                                                                \n\
        \    ┌──────────────────┐                                                        \n\
        \    │ { x = a, x = b } │                                                        \n\
        \    └──────────────────┘                                                        \n\
        \                                                                                \n\
        \                                                                                \n\
        \... is syntactic sugar for:                                                     \n\
        \                                                                                \n\
        \                                                                                \n\
        \    ┌───────────────┐                                                           \n\
        \    │ { x = a ∧ b } │                                                           \n\
        \    └───────────────┘                                                           \n\
        \                                                                                \n\
        \                                                                                \n\
        \... which is rejected if ❰a ∧ b❱ does not type-check.  One way this can happen  \n\
        \is if ❰a❱ and ❰b❱ share a field in common that is not a record, which is known  \n\
        \as a \"collision\".                                                               \n\
        \                                                                                \n\
        \For example, the following expression is " <> _NOT <> " valid:                  \n\
        \                                                                                \n\
        \                                                                                \n\
        \    ┌──────────────────────────────────┐                                        \n\
        \    │ { x = { y = 0 }, x = { y = 1 } } │ Invalid: The two ❰x.y❱ fields \"collide\"\n\
        \    └──────────────────────────────────┘                                        \n\
        \                                                                                \n\
        \                                                                                \n\
        \... whereas the following expression is valid:                                  \n\
        \                                                                                \n\
        \                                                                                \n\
        \    ┌──────────────────────────────────┐                                        \n\
        \    │ { x = { y = 0 }, x = { z = 1 } } │ Valid: the two ❰x❱ fields don't collide\n\
        \    └──────────────────────────────────┘ because they can be recursively merged \n\
        \                                                                                \n\
        \                                                                                \n\
        \Some common reasons why you might get this error:                               \n\
        \                                                                                \n\
        \● You specified the same field twice by mistake                                 \n\
        \                                                                                \n\
        \────────────────────────────────────────────────────────────────────────────────\n\
        \                                                                                \n\
        \You specified the following field twice:                                        \n\
        \                                                                                \n\
        \" <> txt0 <> "\n\
        \                                                                                \n\
        \... which collided on the following path:                                       \n\
        \                                                                                \n\
        \" <> txt1 <> "\n"
      where
        txt0 = insert (Dhall.Pretty.Internal.escapeLabel True (NonEmpty.head ks))

        txt1 = insert (toPath ks)

prettyTypeMessage (FieldCollision ks) = ErrorMessages {..}
  where
    short = "Field collision on: " <> pretty (toPath ks)

    hints = []

    long =
        "Explanation: You can recursively merge records using the ❰∧❱ operator:          \n\
        \                                                                                \n\
        \                                                                                \n\
        \    ┌───────────────────────┐                                                   \n\
        \    │ { x = a } ∧ { y = b } │                                                   \n\
        \    └───────────────────────┘                                                   \n\
        \                                                                                \n\
        \... but two records cannot be merged in this way if they share a field that is  \n\
        \not a record.                                                                   \n\
        \                                                                                \n\
        \For example, the following expressions are " <> _NOT <> " valid:                \n\
        \                                                                                \n\
        \                                                                                \n\
        \    ┌──────────────────────────┐                                                \n\
        \    │ { x = 1 } ∧ { x = True } │  Invalid: The ❰x❱ fields \"collide\" because they\n\
        \    └──────────────────────────┘  are not records that can be merged            \n\
        \                                                                                \n\
        \                                                                                \n\
        \    ┌──────────────────────────────────┐                                        \n\
        \    │ { x = 1 } ∧ { x = { y = True } } │  Invalid: One of the two ❰x❱ fields is \n\
        \    └──────────────────────────────────┘  still not a record                    \n\
        \                                                                                \n\
        \                                                                                \n\
        \... but the following expression is valid:                                      \n\
        \                                                                                \n\
        \                                                                                \n\
        \    ┌──────────────────────────────────────────┐  Valid: The two ❰x❱ fields     \n\
        \    │ { x = { y = True } } ∧ { x = { z = 1 } } │  don't collide because they can\n\
        \    └──────────────────────────────────────────┘  be recursively merged         \n\
        \                                                                                \n\
        \                                                                                \n\
        \Some common reasons why you might get this error:                               \n\
        \                                                                                \n\
        \● You tried to use ❰∧❱ to update a field's value, like this:                    \n\
        \                                                                                \n\
        \                                                                                \n\
        \    ┌────────────────────────────────────────┐                                  \n\
        \    │ { foo = 1, bar = \"ABC\" } ∧ { foo = 2 } │                                  \n\
        \    └────────────────────────────────────────┘                                  \n\
        \                                   ⇧                                            \n\
        \                                  Invalid attempt to update ❰foo❱'s value to ❰2❱\n\
        \                                                                                \n\
        \                                                                                \n\
        \  You probably meant to use ❰⫽❱ / ❰//❱  instead:                                \n\
        \                                                                                \n\
        \                                                                                \n\
        \    ┌────────────────────────────────────────┐                                  \n\
        \    │ { foo = 1, bar = \"ABC\" } ⫽ { foo = 2 } │                                  \n\
        \    └────────────────────────────────────────┘                                  \n\
        \                                                                                \n\
        \                                                                                \n\
        \────────────────────────────────────────────────────────────────────────────────\n\
        \                                                                                \n\
        \You tried to merge two records which collided on the following path:            \n\
        \                                                                                \n\
        \" <> txt0 <> "\n"
      where
        txt0 = insert (toPath ks)

prettyTypeMessage (FieldTypeCollision ks) = ErrorMessages {..}
  where
    short = "Field type collision on: " <> pretty (toPath ks)

    hints = []

    long =
        "Explanation: You can recursively merge record types using the ❰⩓❱ operator, like\n\
        \this:                                                                           \n\
        \                                                                                \n\
        \                                                                                \n\
        \    ┌───────────────────────┐                                                   \n\
        \    │ { x : A } ⩓ { y : B } │                                                   \n\
        \    └───────────────────────┘                                                   \n\
        \                                                                                \n\
        \                                                                                \n\
        \... but you cannot merge record types if two field types collide that are not   \n\
        \both record types.                                                              \n\
        \                                                                                \n\
        \For example, the following expression is " <> _NOT <> " valid:                  \n\
        \                                                                                \n\
        \                                                                                \n\
        \    ┌────────────────────────────────┐                                          \n\
        \    │ { x : Natural } ⩓ { x : Bool } │  Invalid: The ❰x❱ fields \"collide\"       \n\
        \    └────────────────────────────────┘  because they cannot be merged           \n\
        \                                                                                \n\
        \                                                                                \n\
        \... but the following expression is valid:                                      \n\
        \                                                                                \n\
        \                                                                                \n\
        \    ┌────────────────────────────────────────────────┐  Valid: The ❰x❱ field    \n\
        \    │ { x : { y : Bool } } ⩓ { x : { z : Natural } } │  types don't collide and \n\
        \    └────────────────────────────────────────────────┘  can be merged           \n\
        \                                                                                \n\
        \                                                                                \n\
        \────────────────────────────────────────────────────────────────────────────────\n\
        \                                                                                \n\
        \You tried to merge two record types which collided on the following path:       \n\
        \                                                                                \n\
        \" <> txt0 <> "\n"
      where
        txt0 = insert (toPath ks)

prettyTypeMessage (MustMergeARecord expr0 expr1) = ErrorMessages {..}
  where
    short = "❰merge❱ expects a record of handlers"

    hints = []

    long =
        "Explanation: You can ❰merge❱ the alternatives of a union or an ❰Optional❱ using \n\
        \a record with one handler per alternative, like this:                           \n\
        \                                                                                \n\
        \                                                                                \n\
        \    ┌─────────────────────────────────────────────────────────────────────┐     \n\
        \    │     let union    = < Left : Natural | Right : Bool >.Left 2         │     \n\
        \    │ in  let handlers = { Left = Natural/even, Right = λ(x : Bool) → x } │     \n\
        \    │ in  merge handlers union                                            │     \n\
        \    └─────────────────────────────────────────────────────────────────────┘     \n\
        \                                                                                \n\
        \                                                                                \n\
        \... but the first argument to ❰merge❱ must be a record and not some other type. \n\
        \                                                                                \n\
        \For example, the following expression is " <> _NOT <> " valid:                  \n\
        \                                                                                \n\
        \                                                                                \n\
        \    ┌─────────────────────────────────────────────┐                             \n\
        \    │ let handler = λ(x : Bool) → x               │                             \n\
        \    │ in  merge handler (< Foo : Bool >.Foo True) │                             \n\
        \    └─────────────────────────────────────────────┘                             \n\
        \                ⇧                                                               \n\
        \                Invalid: ❰handler❱ isn't a record                               \n\
        \                                                                                \n\
        \                                                                                \n\
        \Some common reasons why you might get this error:                               \n\
        \                                                                                \n\
        \● You accidentally provide an empty record type instead of an empty record when \n\
        \  you ❰merge❱ an empty union:                                                   \n\
        \                                                                                \n\
        \                                                                                \n\
        \    ┌──────────────────────────────────────────┐                                \n\
        \    │ λ(x : <>) → λ(a : Type) → merge {} x : a │                                \n\
        \    └──────────────────────────────────────────┘                                \n\
        \                                      ⇧                                         \n\
        \                                      This should be ❰{=}❱ instead              \n\
        \                                                                                \n\
        \                                                                                \n\
        \────────────────────────────────────────────────────────────────────────────────\n\
        \                                                                                \n\
        \You provided the following handler:                                             \n\
        \                                                                                \n\
        \" <> txt0 <> "\n\
        \                                                                                \n\
        \... which is not a record, but is actually a value of type:                     \n\
        \                                                                                \n\
        \" <> txt1 <> "\n"
      where
        txt0 = insert expr0
        txt1 = insert expr1

prettyTypeMessage (MustMergeUnionOrOptional expr0 expr1) = ErrorMessages {..}
  where
    short = "❰merge❱ expects a union or an ❰Optional❱"

    hints = []

    long =
        "Explanation: You can ❰merge❱ the alternatives of a union or an ❰Optional❱ using \n\
        \a record with one handler per alternative, like this:                           \n\
        \                                                                                \n\
        \                                                                                \n\
        \    ┌─────────────────────────────────────────────────────────────────┐         \n\
        \    │ let union    = < Left : Natural | Right : Bool >.Left 2         │         \n\
        \    │ let handlers = { Left = Natural/even, Right = λ(x : Bool) → x } │         \n\
        \    │ in  merge handlers union                                        │         \n\
        \    └─────────────────────────────────────────────────────────────────┘         \n\
        \                                                                                \n\
        \                                                                                \n\
        \... or this:                                                                    \n\
        \                                                                                \n\
        \                                                                                \n\
        \    ┌─────────────────────────────────────────────────────────┐                 \n\
        \    │ let optional = None Bool                                │                 \n\
        \    │ let handlers = { None = False, Some = λ(x : Bool) → x } │                 \n\
        \    │ in  merge handlers optional                             │                 \n\
        \    └─────────────────────────────────────────────────────────┘                 \n\
        \                                                                                \n\
        \                                                                                \n\
        \... but the second argument to ❰merge❱ must not be some other type.             \n\
        \                                                                                \n\
        \For example, the following expression is " <> _NOT <> " valid:                  \n\
        \                                                                                \n\
        \                                                                                \n\
        \    ┌──────────────────────────────────────────┐                                \n\
        \    │ let handlers = { Foo = λ(x : Bool) → x } │                                \n\
        \    │ in  merge handlers True                  │                                \n\
        \    └──────────────────────────────────────────┘                                \n\
        \                         ⇧                                                      \n\
        \                         Invalid: ❰True❱ isn't a union or an ❰Optional❱         \n\
        \                                                                                \n\
        \                                                                                \n\
        \You tried to ❰merge❱ this expression:                                           \n\
        \                                                                                \n\
        \" <> txt0 <> "\n\
        \                                                                                \n\
        \... which is not a union or an ❰Optional❱, but is actually a value of type:     \n\
        \                                                                                \n\
        \" <> txt1 <> "\n"
      where
        txt0 = insert expr0
        txt1 = insert expr1

prettyTypeMessage (UnusedHandler ks) = ErrorMessages {..}
  where
    short = "Unused handler"

    hints = []

    long =
        "Explanation: You can ❰merge❱ the alternatives of a union or an ❰Optional❱ using \n\
        \a record with one handler per alternative, like this:                           \n\
        \                                                                                \n\
        \                                                                                \n\
        \    ┌─────────────────────────────────────────────────────────────────┐         \n\
        \    │ let union    = < Left : Natural | Right : Bool >.Left 2         │         \n\
        \    │ let handlers = { Left = Natural/even, Right = λ(x : Bool) → x } │         \n\
        \    │ in  merge handlers union                                        │         \n\
        \    └─────────────────────────────────────────────────────────────────┘         \n\
        \                                                                                \n\
        \                                                                                \n\
        \... but you must provide exactly one handler per alternative in the union.  You \n\
        \cannot supply extra handlers                                                    \n\
        \                                                                                \n\
        \For example, the following expression is " <> _NOT <> " valid:                  \n\
        \                                                                                \n\
        \                                                                                \n\
        \    ┌──────────────────────────────────────────┐                                \n\
        \    │ let union    = < Left : Natural >.Left 2 │  The ❰Right❱ alternative is    \n\
        \    │ let handlers =                           │  missing                       \n\
        \    │             { Left  = Natural/even       │                                \n\
        \    │             , Right = λ(x : Bool) → x    │  Invalid: ❰Right❱ handler isn't\n\
        \    │             }                            │           used                 \n\
        \    │ in  merge handlers union                 │                                \n\
        \    └──────────────────────────────────────────┘                                \n\
        \                                                                                \n\
        \                                                                                \n\
        \You provided the following handlers:                                            \n\
        \                                                                                \n\
        \" <> txt0 <> "\n\
        \                                                                                \n\
        \... which had no matching alternatives in the union you tried to ❰merge❱        \n"
      where
        txt0 = insert (Text.intercalate ", " (Data.Set.toList ks))

prettyTypeMessage (MissingHandler exemplar ks) = ErrorMessages {..}
  where
    short = case Data.Set.toList ks of
         []       -> "Missing handler: " <> Dhall.Pretty.Internal.prettyLabel exemplar
         xs@(_:_) -> "Missing handlers: " <> (Pretty.hsep . Pretty.punctuate Pretty.comma
                                             . map Dhall.Pretty.Internal.prettyLabel $ exemplar:xs)

    hints = []

    long =
        "Explanation: You can ❰merge❱ the alternatives of a union or an ❰Optional❱ using \n\
        \a record with one handler per alternative, like this:                           \n\
        \                                                                                \n\
        \                                                                                \n\
        \    ┌─────────────────────────────────────────────────────────────────┐         \n\
        \    │ let union    = < Left : Natural | Right : Bool >.Left 2         │         \n\
        \    │ let handlers = { Left = Natural/even, Right = λ(x : Bool) → x } │         \n\
        \    │ in  merge handlers union                                        │         \n\
        \    └─────────────────────────────────────────────────────────────────┘         \n\
        \                                                                                \n\
        \                                                                                \n\
        \... but you must provide exactly one handler per alternative in the union.  You \n\
        \cannot omit any handlers                                                        \n\
        \                                                                                \n\
        \For example, the following expression is " <> _NOT <> " valid:                  \n\
        \                                                                                \n\
        \                                                                                \n\
        \                                          Invalid: Missing ❰Right❱ handler      \n\
        \                                          ⇩                                     \n\
        \    ┌──────────────────────────────────────────────────────────────┐            \n\
        \    │ let handlers = { Left = Natural/even }                       │            \n\
        \    │ let union    = < Left : Natural | Right : Bool >.Left 2      │            \n\
        \    │ in  merge handlers union                                     │            \n\
        \    └──────────────────────────────────────────────────────────────┘            \n\
        \                                                                                \n\
        \                                                                                \n\
        \Note that you need to provide handlers for other alternatives even if those     \n\
        \alternatives are never used                                                     \n\
        \                                                                                \n\
        \You need to supply the following handlers:                                      \n\
        \                                                                                \n\
        \" <> txt0 <> "\n"
      where
        txt0 = insert (Text.intercalate ", " (exemplar : Data.Set.toList ks))

prettyTypeMessage MissingMergeType =
    ErrorMessages {..}
  where
    short = "An empty ❰merge❱ requires a type annotation"

    hints = []

    long =
        "Explanation: A ❰merge❱ does not require a type annotation if the union has at   \n\
        \least one alternative, like this                                                \n\
        \                                                                                \n\
        \                                                                                \n\
        \    ┌─────────────────────────────────────────────────────────────────┐         \n\
        \    │ let union    = < Left : Natural | Right : Bool >.Left 2         │         \n\
        \    │ let handlers = { Left = Natural/even, Right = λ(x : Bool) → x } │         \n\
        \    │ in  merge handlers union                                        │         \n\
        \    └─────────────────────────────────────────────────────────────────┘         \n\
        \                                                                                \n\
        \                                                                                \n\
        \However, you must provide a type annotation when merging an empty union:        \n\
        \                                                                                \n\
        \                                                                                \n\
        \    ┌────────────────────────────────┐                                          \n\
        \    │ λ(a : <>) → merge {=} a : Bool │                                          \n\
        \    └────────────────────────────────┘                                          \n\
        \                                ⇧                                               \n\
        \                                This can be any type                            \n\
        \                                                                                \n\
        \                                                                                \n\
        \You can provide any type at all as the annotation, since merging an empty       \n\
        \union can produce any type of output                                            \n"

prettyTypeMessage (HandlerInputTypeMismatch expr0 expr1 expr2) =
    ErrorMessages {..}
  where
    short = "Wrong handler input type\n"
        <>  "\n"
        <>  Dhall.Diff.doc (Dhall.Diff.diffNormalized expr1 expr2)

    hints = []

    long =
        "Explanation: You can ❰merge❱ the alternatives of a union or an ❰Optional❱ using \n\
        \a record with one handler per alternative, like this:                           \n\
        \                                                                                \n\
        \                                                                                \n\
        \    ┌─────────────────────────────────────────────────────────────────┐         \n\
        \    │ let union    = < Left : Natural | Right : Bool >.Left 2         │         \n\
        \    │ let handlers = { Left = Natural/even, Right = λ(x : Bool) → x } │         \n\
        \    │ in  merge handlers union                                        │         \n\
        \    └─────────────────────────────────────────────────────────────────┘         \n\
        \                                                                                \n\
        \                                                                                \n\
        \... as long as the input type of each handler function matches the type of the  \n\
        \corresponding alternative:                                                      \n\
        \                                                                                \n\
        \                                                                                \n\
        \    ┌───────────────────────────────────────────────────────────┐               \n\
        \    │ union    : < Left : Natural       | Right : Bool        > │               \n\
        \    └───────────────────────────────────────────────────────────┘               \n\
        \                          ⇧                       ⇧                             \n\
        \                   These must match        These must match                     \n\
        \                          ⇩                       ⇩                             \n\
        \    ┌───────────────────────────────────────────────────────────┐               \n\
        \    │ handlers : { Left : Natural → Bool, Right : Bool → Bool } │               \n\
        \    └───────────────────────────────────────────────────────────┘               \n\
        \                                                                                \n\
        \                                                                                \n\
        \For example, the following expression is " <> _NOT <> " valid:                  \n\
        \                                                                                \n\
        \                                                                                \n\
        \      Invalid: Doesn't match the type of the ❰Right❱ alternative                \n\
        \                                                               ⇩                \n\
        \    ┌──────────────────────────────────────────────────────────────────┐        \n\
        \    │ let handlers = { Left = Natural/even | Right = λ(x : Text) → x } │        \n\
        \    │ let union    = < Left : Natural | Right : Bool >.Left 2          │        \n\
        \    │ in  merge handlers union                                         │        \n\
        \    └──────────────────────────────────────────────────────────────────┘        \n\
        \                                                                                \n\
        \                                                                                \n\
        \Your handler for the following alternative:                                     \n\
        \                                                                                \n\
        \" <> txt0 <> "\n\
        \                                                                                \n\
        \... needs to accept an input value of type:                                     \n\
        \                                                                                \n\
        \" <> txt1 <> "\n\
        \                                                                                \n\
        \... but actually accepts an input value of a different type:                    \n\
        \                                                                                \n\
        \" <> txt2 <> "\n"
      where
        txt0 = insert expr0
        txt1 = insert expr1
        txt2 = insert expr2

prettyTypeMessage (DisallowedHandlerType label handlerType handlerOutputType variable) =
    ErrorMessages {..}
  where
    short = "Disallowed handler type"

    hints = []

    long =
        "Explanation: You can ❰merge❱ the alternatives of a union or an ❰Optional❱ using \n\
        \a record with one handler per alternative, like this:                           \n\
        \                                                                                \n\
        \                                                                                \n\
        \    ┌─────────────────────────────────────────────────────────────────┐         \n\
        \    │ let union    = < Left : Natural | Right : Bool >.Left 2         │         \n\
        \    │ let handlers = { Left = Natural/even, Right = λ(x : Bool) → x } │         \n\
        \    │ in  merge handlers union                                        │         \n\
        \    └─────────────────────────────────────────────────────────────────┘         \n\
        \                                                                                \n\
        \                                                                                \n\
        \... but the output type of a handler may not depend on the input value.         \n\
        \                                                                                \n\
        \For example, the following expression is " <> _NOT <> " valid:                  \n\
        \                                                                                \n\
        \                                                                                \n\
        \      Invalid: The output type is ❰Optional A❱, which references the input      \n\
        \      value ❰A❱.                                                                \n\
        \                  ⇩                                                             \n\
        \    ┌──────────────────────────────────────────┐                                \n\
        \    │ merge { x = None } (< x : Type >.x Bool) │                                \n\
        \    └──────────────────────────────────────────┘                                \n\
        \                                                                                \n\
        \                                                                                \n\
        \Your handler for the following alternative:                                     \n\
        \                                                                                \n\
        \" <> insert label <> "\n\
        \                                                                                \n\
        \... has type:                                                                   \n\
        \                                                                                \n\
        \" <> insert handlerType <> "\n\
        \                                                                                \n\
        \... where the output type:                                                      \n\
        \                                                                                \n\
        \" <> insert handlerOutputType <> "\n\
        \                                                                                \n\
        \... references the handler's input value:                                       \n\
        \                                                                                \n\
        \" <> insert variable <> "\n"

prettyTypeMessage (InvalidHandlerOutputType expr0 expr1 expr2) =
    ErrorMessages {..}
  where
    short = "Wrong handler output type\n"
        <>  "\n"
        <>  Dhall.Diff.doc (Dhall.Diff.diffNormalized expr1 expr2)

    hints = []

    long =
        "Explanation: You can ❰merge❱ the alternatives of a union or an ❰Optional❱ using \n\
        \a record with one handler per alternative, like this:                           \n\
        \                                                                                \n\
        \                                                                                \n\
        \    ┌─────────────────────────────────────────────────────────────────┐         \n\
        \    │ let union    = < Left : Natural | Right : Bool >.Left 2         │         \n\
        \    │ let handlers = { Left = Natural/even, Right = λ(x : Bool) → x } │         \n\
        \    │ in  merge handlers union : Bool                                 │         \n\
        \    └─────────────────────────────────────────────────────────────────┘         \n\
        \                                                                                \n\
        \                                                                                \n\
        \... as long as the output type of each handler function matches the declared    \n\
        \type of the result:                                                             \n\
        \                                                                                \n\
        \                                                                                \n\
        \    ┌───────────────────────────────────────────────────────────┐               \n\
        \    │ handlers : { Left : Natural → Bool, Right : Bool → Bool } │               \n\
        \    └───────────────────────────────────────────────────────────┘               \n\
        \                                    ⇧                    ⇧                      \n\
        \                                    These output types ...                      \n\
        \                                                                                \n\
        \                             ... must match the declared type of the ❰merge❱    \n\
        \                             ⇩                                                  \n\
        \    ┌─────────────────────────────┐                                             \n\
        \    │ merge handlers union : Bool │                                             \n\
        \    └─────────────────────────────┘                                             \n\
        \                                                                                \n\
        \                                                                                \n\
        \For example, the following expression is " <> _NOT <> " valid:                  \n\
        \                                                                                \n\
        \                                                                                \n\
        \    ┌──────────────────────────────────────────────────────────────────┐        \n\
        \    │ let union    = < Left : Natural | Right : Bool >.Left 2          │        \n\
        \    │ let handlers = { Left = Natural/even, Right = λ(x : Bool) → x }  │        \n\
        \    │ in  merge handlers union : Text                                  │        \n\
        \    └──────────────────────────────────────────────────────────────────┘        \n\
        \                                 ⇧                                              \n\
        \                                 Invalid: Doesn't match output of either handler\n\
        \                                                                                \n\
        \                                                                                \n\
        \Your handler for the following alternative:                                     \n\
        \                                                                                \n\
        \" <> txt0 <> "\n\
        \                                                                                \n\
        \... needs to return an output value of type:                                    \n\
        \                                                                                \n\
        \" <> txt1 <> "\n\
        \                                                                                \n\
        \... but actually returns an output value of a different type:                   \n\
        \                                                                                \n\
        \" <> txt2 <> "\n"
      where
        txt0 = insert expr0
        txt1 = insert expr1
        txt2 = insert expr2

prettyTypeMessage (HandlerOutputTypeMismatch key0 expr0 key1 expr1) =
    ErrorMessages {..}
  where
    short = "Handlers should have the same output type\n"
        <>  "\n"
        <>  Dhall.Diff.doc (Dhall.Diff.diffNormalized expr0 expr1)

    hints = []

    long =
        "Explanation: You can ❰merge❱ the alternatives of a union or an ❰Optional❱ using \n\
        \a record with one handler per alternative, like this:                           \n\
        \                                                                                \n\
        \                                                                                \n\
        \    ┌─────────────────────────────────────────────────────────────────┐         \n\
        \    │ let union    = < Left : Natural | Right : Bool >.Left 2         │         \n\
        \    │ let handlers = { Left = Natural/even, Right = λ(x : Bool) → x } │         \n\
        \    │ in  merge handlers union                                        │         \n\
        \    └─────────────────────────────────────────────────────────────────┘         \n\
        \                                                                                \n\
        \                                                                                \n\
        \... as long as the output type of each handler function is the same:            \n\
        \                                                                                \n\
        \                                                                                \n\
        \    ┌───────────────────────────────────────────────────────────┐               \n\
        \    │ handlers : { Left : Natural → Bool, Right : Bool → Bool } │               \n\
        \    └───────────────────────────────────────────────────────────┘               \n\
        \                                    ⇧                    ⇧                      \n\
        \                                These output types both match                   \n\
        \                                                                                \n\
        \                                                                                \n\
        \For example, the following expression is " <> _NOT <> " valid:                  \n\
        \                                                                                \n\
        \                                                                                \n\
        \    ┌─────────────────────────────────────────────────┐                         \n\
        \    │ let Union = < Left : Natural | Right : Bool >   │                         \n\
        \    │ let handlers =                                  │                         \n\
        \    │              { Left  = λ(x : Natural) → x       │  This outputs ❰Natural❱ \n\
        \    │              , Right = λ(x : Bool   ) → x       │  This outputs ❰Bool❱    \n\
        \    │              }                                  │                         \n\
        \    │ in  merge handlers (Union.Left 2)               │                         \n\
        \    └─────────────────────────────────────────────────┘                         \n\
        \                ⇧                                                               \n\
        \                Invalid: The handlers in this record don't have matching outputs\n\
        \                                                                                \n\
        \                                                                                \n\
        \The handler for the ❰" <> txt0 <> "❱ alternative has this output type:          \n\
        \                                                                                \n\
        \" <> txt1 <> "\n\
        \                                                                                \n\
        \... but the handler for the ❰" <> txt2 <> "❱ alternative has this output type instead:\n\
        \                                                                                \n\
        \" <> txt3 <> "\n"
      where
        txt0 = pretty key0
        txt1 = insert expr0
        txt2 = pretty key1
        txt3 = insert expr1

prettyTypeMessage (HandlerNotAFunction k expr0) = ErrorMessages {..}
  where
    short = "Handler for "<> Dhall.Pretty.Internal.prettyLabel k <> " is not a function"

    hints = []

    long =
        "Explanation: You can ❰merge❱ the alternatives of a union or an ❰Optional❱ using \n\
        \a record with one handler per alternative, like this:                           \n\
        \                                                                                \n\
        \                                                                                \n\
        \    ┌─────────────────────────────────────────────────────────────────┐         \n\
        \    │ let union    = < Left : Natural | Right : Bool >.Left 2         │         \n\
        \    │ let handlers = { Left = Natural/even, Right = λ(x : Bool) → x } │         \n\
        \    │ in  merge handlers union                                        │         \n\
        \    └─────────────────────────────────────────────────────────────────┘         \n\
        \                                                                                \n\
        \                                                                                \n\
        \... as long as each handler is a function -- FIXME                              \n\
        \                                                                                \n\
        \For example, the following expression is " <> _NOT <> " valid:                  \n\
        \                                                                                \n\
        \                                                                                \n\
        \    ┌────────────────────────────────────────────────┐                          \n\
        \    │ merge { Foo = True } (< Foo : Natural >.Foo 1) │                          \n\
        \    └────────────────────────────────────────────────┘                          \n\
        \                    ⇧                                                           \n\
        \                    Invalid: Not a function                                     \n\
        \                                                                                \n\
        \                                                                                \n\
        \Your handler for this alternative:                                              \n\
        \                                                                                \n\
        \" <> txt0 <> "\n\
        \                                                                                \n\
        \... has the following type:                                                     \n\
        \                                                                                \n\
        \" <> txt1 <> "\n\
        \                                                                                \n\
        \... which is not the type of a function                                         \n"
      where
        txt0 = insert k
        txt1 = insert expr0

prettyTypeMessage (MustMapARecord provided _providedType) = ErrorMessages {..}
  where
    short = "❰toMap❱ expects a record value"

    hints = emptyRecordTypeHint provided

    long =
        "Explanation: You can apply ❰toMap❱ to any homogenous record, like this:         \n\
        \                                                                                \n\
        \                                                                                \n\
        \    ┌─────────────────────────────────────────────────────────────────────┐     \n\
        \    │ let record = { one = 1, two = 2 }                                   │     \n\
        \    │ in  toMap record : List { mapKey : Text, mapValue : Natural}        │     \n\
        \    └─────────────────────────────────────────────────────────────────────┘     \n\
        \                                                                                \n\
        \                                                                                \n\
        \... but the argument to ❰toMap❱ must be a record and not some other type.       \n\
        \                                                                                \n\
        \Some common reasons why you might get this error:                               \n\
        \                                                                                \n\
        \● You accidentally provide an empty record type instead of an empty record when \n\
        \  using ❰toMap❱:                                                                \n\
        \                                                                                \n\
        \                                                                                \n\
        \    ┌───────────────────────────────────────────────────────┐                   \n\
        \    │ toMap {} : List { mapKey : Text, mapValue : Natural } │                   \n\
        \    └───────────────────────────────────────────────────────┘                   \n\
        \            ⇧                                                                   \n\
        \            This should be ❰{=}❱ instead                                        \n"

prettyTypeMessage (InvalidToMapRecordKind type_ kind) = ErrorMessages {..}
  where
    short = "❰toMap❱ expects a record of kind ❰Type❱"

    hints = []

    long =
        "Explanation: You can apply ❰toMap❱ to any homogenous record of kind ❰Type❱, like\n\
        \ this:                                                                          \n\
        \                                                                                \n\
        \                                                                                \n\
        \    ┌─────────────────────────────────────────────────────────────────────┐     \n\
        \    │ let record = { one = 1, two = 2 }                                   │     \n\
        \    │ in  toMap record : List { mapKey : Text, mapValue : Natural}        │     \n\
        \    └─────────────────────────────────────────────────────────────────────┘     \n\
        \                                                                                \n\
        \                                                                                \n\
        \... but records of kind ❰Kind❱ or ❰Sort❱ cannot be turned into ❰List❱s.         \n\
        \────────────────────────────────────────────────────────────────────────────────\n\
        \                                                                                \n\
        \You applied ❰toMap❱ to a record of the following type:                          \n\
        \                                                                                \n\
        \" <> insert type_ <> "\n\
        \                                                                                \n\
        \... which has kind                                                              \n\
        \                                                                                \n\
        \" <> insert kind <> "\n"

prettyTypeMessage (HeterogenousRecordToMap _expr0 _expr1 _expr2) = ErrorMessages {..}
  where
    short = "❰toMap❱ expects a homogenous record"

    hints = []

    long =
        "Explanation: You can apply ❰toMap❱ to any homogenous record, like this:         \n\
        \                                                                                \n\
        \                                                                                \n\
        \    ┌─────────────────────────────────────────────────────────────────────┐     \n\
        \    │ let record = { one = 1, two = 2 }                                   │     \n\
        \    │ in  toMap record : List { mapKey : Text, mapValue : Natural}        │     \n\
        \    └─────────────────────────────────────────────────────────────────────┘     \n\
        \                                                                                \n\
        \                                                                                \n\
        \... but every field of the record must have the same type.                      \n\
        \                                                                                \n\
        \For example, the following expression is " <> _NOT <> " valid:                  \n\
        \                                                                                \n\
        \                                                                                \n\
        \    ┌─────────────────────────────────────────┐                                 \n\
        \    │ toMap { Foo = True, Bar = 0 }           │                                 \n\
        \    └─────────────────────────────────────────┘                                 \n\
        \                    ⇧           ⇧                                               \n\
        \                    Bool        Natural                                         \n"

prettyTypeMessage (MapTypeMismatch expr0 expr1) = ErrorMessages {..}
  where
    short = "❰toMap❱ result type doesn't match annotation"
        <>  "\n"
        <>  Dhall.Diff.doc (Dhall.Diff.diffNormalized expr0 expr1)

    hints = []

    long =
        "Explanation: a ❰toMap❱ application has been annotated with a type that doesn't  \n\
        \match its inferred type.                                                        \n"

prettyTypeMessage (InvalidToMapType expr) =
    ErrorMessages {..}
  where
    short = "An empty ❰toMap❱ was annotated with an invalid type"
        <>  "\n"
        <>  insert expr

    hints = []

    long =
        "Explanation: A ❰toMap❱ applied to an empty record must have a type annotation:  \n\
        \that matches a list of key-value pairs, like this                               \n\
        \                                                                                \n\
        \                                                                                \n\
        \    ┌─────────────────────────────────────────────────────────────────────┐     \n\
        \    │ toMap {=} : List { mapKey : Text, mapValue : Natural}               │     \n\
        \    └─────────────────────────────────────────────────────────────────────┘     \n\
        \                                                                                \n\
        \The type you have provided doesn't match the expected form.                     \n\
        \                                                                                \n"

prettyTypeMessage MissingToMapType =
    ErrorMessages {..}
  where
    short = "An empty ❰toMap❱ requires a type annotation"

    hints = []

    long =
        "Explanation: A ❰toMap❱ does not require a type annotation if the record has at  \n\
        \least one field, like this                                                      \n\
        \                                                                                \n\
        \                                                                                \n\
        \    ┌─────────────────────────────────────────────────────────────────────┐     \n\
        \    │ let record = { one = 1, two = 2 }                                   │     \n\
        \    │ in  toMap record                                                    │     \n\
        \    └─────────────────────────────────────────────────────────────────────┘     \n\
        \                                                                                \n\
        \                                                                                \n\
        \However, you must provide a type annotation with an empty record:               \n\
        \                                                                                \n\
        \                                                                                \n\
        \    ┌─────────────────────────────────────────────────────────────────────┐     \n\
        \    │ toMap {=} : List { mapKey : Text, mapValue : Natural}               │     \n\
        \    └─────────────────────────────────────────────────────────────────────┘     \n\
        \                                                                                \n"

prettyTypeMessage (CantAccess lazyText0 expr0 expr1) = ErrorMessages {..}
  where
    short = "Not a record or a union"

    hints = []

    long =
        "Explanation: You can only access fields on records or unions, like this:        \n\
        \                                                                                \n\
        \                                                                                \n\
        \    ┌─────────────────────────────────┐                                         \n\
        \    │ { foo = True, bar = \"ABC\" }.foo │  This is valid ...                    \n\
        \    └─────────────────────────────────┘                                         \n\
        \                                                                                \n\
        \                                                                                \n\
        \    ┌───────────────────────────────────────────┐                               \n\
        \    │ λ(r : { foo : Bool, bar : Text }) → r.foo │  ... and so is this           \n\
        \    └───────────────────────────────────────────┘                               \n\
        \                                                                                \n\
        \                                                                                \n\
        \    ┌─────────────────────────────────┐                                         \n\
        \    │ < foo : Bool | bar : Text >.foo │  ... and so is this                     \n\
        \    └─────────────────────────────────┘                                         \n\
        \                                                                                \n\
        \                                                                                \n\
        \    ┌────────────────────────────────────────────┐                              \n\
        \    │ λ(r : < foo : Bool | bar : Text >) → r.foo │  ... and so is this          \n\
        \    └────────────────────────────────────────────┘                              \n\
        \                                                                                \n\
        \                                                                                \n\
        \... but you cannot access fields on non-record expressions                      \n\
        \                                                                                \n\
        \For example, the following expression is " <> _NOT <> " valid:                  \n\
        \                                                                                \n\
        \                                                                                \n\
        \    ┌───────┐                                                                   \n\
        \    │ 1.foo │                                                                   \n\
        \    └───────┘                                                                   \n\
        \      ⇧                                                                         \n\
        \      Invalid: Not a record                                                     \n\
        \                                                                                \n\
        \                                                                                \n\
        \────────────────────────────────────────────────────────────────────────────────\n\
        \                                                                                \n\
        \You tried to access the field:                                                  \n\
        \                                                                                \n\
        \" <> txt0 <> "\n\
        \                                                                                \n\
        \... on the following expression which is not a record nor a union type:         \n\
        \                                                                                \n\
        \" <> txt1 <> "\n\
        \                                                                                \n\
        \... but is actually an expression of type:                                      \n\
        \                                                                                \n\
        \" <> txt2 <> "\n"
      where
        txt0 = insert lazyText0
        txt1 = insert expr0
        txt2 = insert expr1

prettyTypeMessage (CantProject lazyText0 expr0 expr1) = ErrorMessages {..}
  where
    short = "Not a record"

    hints = []

    long =
        "Explanation: You can only project fields on records, like this:                 \n\
        \                                                                                \n\
        \                                                                                \n\
        \    ┌─────────────────────────────────────────────────────┐                     \n\
        \    │ { foo = True, bar = \"ABC\", baz = 1 }.{ foo, bar } │  This is valid ...  \n\
        \    └─────────────────────────────────────────────────────┘                     \n\
        \                                                                                \n\
        \                                                                                \n\
        \    ┌────────────────────────────────────────────────────────────────────┐      \n\
        \    │ λ(r : { foo : Bool, bar : Text , baz : Natural }) → r.{ foo, bar } │  ... and so is this           \n\
        \    └────────────────────────────────────────────────────────────────────┘      \n\
        \                                                                                \n\
        \                                                                                \n\
        \... but you cannot project fields on non-record expressions                     \n\
        \                                                                                \n\
        \For example, the following expression is " <> _NOT <> " valid:                  \n\
        \                                                                                \n\
        \                                                                                \n\
        \    ┌────────────────┐                                                          \n\
        \    │ 1.{ foo, bar } │                                                          \n\
        \    └────────────────┘                                                          \n\
        \      ⇧                                                                         \n\
        \      Invalid: Not a record                                                     \n\
        \                                                                                \n\
        \                                                                                \n\
        \Some common reasons why you might get this error:                               \n\
        \                                                                                \n\
        \● You accidentally try to project fields of a union instead of a record, like   \n\
        \  this:                                                                         \n\
        \                                                                                \n\
        \                                                                                \n\
        \    ┌────────────────────────────────────┐                                      \n\
        \    │ < foo : a | bar : b >.{ foo, bar } │                                      \n\
        \    └────────────────────────────────────┘                                      \n\
        \      ⇧                                                                         \n\
        \      This is a union, not a record                                             \n\
        \                                                                                \n\
        \                                                                                \n\
        \────────────────────────────────────────────────────────────────────────────────\n\
        \                                                                                \n\
        \You tried to access the fields:                                                 \n\
        \                                                                                \n\
        \" <> txt0 <> "\n\
        \                                                                                \n\
        \... on the following expression which is not a record:                          \n\
        \                                                                                \n\
        \" <> txt1 <> "\n\
        \                                                                                \n\
        \... but is actually an expression of type:                                      \n\
        \                                                                                \n\
        \" <> txt2 <> "\n"
      where
        txt0 = insert lazyText0
        txt1 = insert expr0
        txt2 = insert expr1

prettyTypeMessage (CantProjectByExpression expr) = ErrorMessages {..}
  where
    short = "Selector is not a record type"

    hints = []

    long =
        "Explanation: You can project by an expression if that expression is a record    \n\
        \type:                                                                           \n\
        \                                                                                \n\
        \    ┌─────────────────────────────────┐                                         \n\
        \    │ { foo = True }.({ foo : Bool }) │  This is valid ...                      \n\
        \    └─────────────────────────────────┘                                         \n\
        \                                                                                \n\
        \                                                                                \n\
        \    ┌──────────────────────────────────────────┐                                \n\
        \    │ λ(r : { foo : Bool }) → r.{ foo : Bool } │  ... and so is this            \n\
        \    └──────────────────────────────────────────┘                                \n\
        \                                                                                \n\
        \                                                                                \n\
        \... but you cannot project by any other type of expression:                     \n\
        \                                                                                \n\
        \For example, the following expression is " <> _NOT <> " valid:                  \n\
        \                                                                                \n\
        \                                                                                \n\
        \    ┌───────────────────────┐                                                   \n\
        \    │ { foo = True }.(True) │                                                   \n\
        \    └───────────────────────┘                                                   \n\
        \                      ⇧                                                         \n\
        \                      Invalid: Not a record type                                \n\
        \                                                                                \n\
        \                                                                                \n\
        \Some common reasons why you might get this error:                               \n\
        \                                                                                \n\
        \● You accidentally try to project by a record value instead of a record type,   \n\
        \  like this:                                                                    \n\
        \                                                                                \n\
        \                                                                                \n\
        \    ┌─────────────────────────────────┐                                         \n\
        \    │ let T = { foo : Bool }          │                                         \n\
        \    │                                 │                                         \n\
        \    │ let x = { foo = True , bar = 1} │                                         \n\
        \    │                                 │                                         \n\
        \    │ let y = { foo = False, bar = 2} │                                         \n\
        \    │                                 │                                         \n\
        \    │ in  x.(y)                       │                                         \n\
        \    └─────────────────────────────────┘                                         \n\
        \             ⇧                                                                  \n\
        \             The user might have meant ❰T❱ here                                 \n\
        \                                                                                \n\
        \                                                                                \n\
        \────────────────────────────────────────────────────────────────────────────────\n\
        \                                                                                \n\
        \You tried to project out the following type:                                    \n\
        \                                                                                \n\
        \" <> txt <> "\n\
        \                                                                                \n\
        \... which is not a record type                                                  \n"
      where
        txt = insert expr

prettyTypeMessage (DuplicateProjectionLabel k) = ErrorMessages {..}
  where
    short = "Duplicate projection label: " <> Dhall.Pretty.Internal.prettyLabel k

    hints = []

    long =
        "Explanation: You can only specify a label once when projecting a record's fields\n\
        \by label.  For example, this is valid:                                          \n\
        \                                                                                \n\
        \                                                                                \n\
        \    ┌─────────────────────────────────────────┐                                 \n\
        \    │ { x = 1.1, y = 2.4, z = -0.3 }.{ x, y } │                                 \n\
        \    └─────────────────────────────────────────┘                                 \n\
        \                                                                                \n\
        \                                                                                \n\
        \... but this is not valid:                                                      \n\
        \                                                                                \n\
        \                                                                                \n\
        \    ┌─────────────────────────────────────────┐                                 \n\
        \    │ { x = 1.1, y = 2.4, z = -0.3 }.{ y, y } │                                 \n\
        \    └─────────────────────────────────────────┘                                 \n\
        \                                          ⇧                                     \n\
        \                                          Invalid: the label ❰y❱ appears twice  \n\
        \                                                                                \n\
        \                                                                                \n\
        \You tried to project the following field twice:                                 \n\
        \                                                                                \n\
        \" <> txt0 <> "\n"
      where
        txt0 = insert k

prettyTypeMessage (MissingField k expr0) = ErrorMessages {..}
  where
    short = "Missing record field: " <> Dhall.Pretty.Internal.prettyLabel k

    hints = []

    long =
        "Explanation: You can only access fields on records, like this:                  \n\
        \                                                                                \n\
        \                                                                                \n\
        \    ┌─────────────────────────────────┐                                         \n\
        \    │ { foo = True, bar = \"ABC\" }.foo │  This is valid ...                    \n\
        \    └─────────────────────────────────┘                                         \n\
        \                                                                                \n\
        \                                                                                \n\
        \    ┌───────────────────────────────────────────┐                               \n\
        \    │ λ(r : { foo : Bool, bar : Text }) → r.foo │  ... and so is this           \n\
        \    └───────────────────────────────────────────┘                               \n\
        \                                                                                \n\
        \                                                                                \n\
        \... but you can only access fields if they are present                          \n\
        \                                                                                \n\
        \For example, the following expression is " <> _NOT <> " valid:                  \n\
        \                                                                                \n\
        \                                                                                \n\
        \    ┌─────────────────────────────────┐                                         \n\
        \    │ { foo = True, bar = \"ABC\" }.qux │                                       \n\
        \    └─────────────────────────────────┘                                         \n\
        \                                  ⇧                                             \n\
        \                                  Invalid: the record has no ❰qux❱ field        \n\
        \                                                                                \n\
        \                                                                                \n\
        \You tried to access a field named:                                              \n\
        \                                                                                \n\
        \" <> txt0 <> "\n\
        \                                                                                \n\
        \... but the field is missing because the record only defines the following      \n\
        \fields:                                                                         \n\
        \                                                                                \n\
        \" <> txt1 <> "\n"
      where
        txt0 = insert k
        txt1 = insert expr0

prettyTypeMessage (MissingConstructor k expr0) = ErrorMessages {..}
  where
    short = "Missing constructor: " <> Dhall.Pretty.Internal.prettyLabel k

    hints = []

    long =
        "Explanation: You can access constructors from unions, like this:                \n\
        \                                                                                \n\
        \                                                                                \n\
        \    ┌───────────────────┐                                                       \n\
        \    │ < Foo | Bar >.Foo │  This is valid ...                                    \n\
        \    └───────────────────┘                                                       \n\
        \                                                                                \n\
        \                                                                                \n\
        \... but you can only access constructors if they match an union alternative of  \n\
        \the same name.                                                                  \n\
        \                                                                                \n\
        \For example, the following expression is " <> _NOT <> " valid:                  \n\
        \                                                                                \n\
        \                                                                                \n\
        \    ┌───────────────────┐                                                       \n\
        \    │ < Foo | Bar >.Baz │                                                       \n\
        \    └───────────────────┘                                                       \n\
        \                    ⇧                                                           \n\
        \                    Invalid: the union has no ❰Baz❱ alternative                 \n\
        \                                                                                \n\
        \                                                                                \n\
        \You tried to access a constructor named:                                        \n\
        \                                                                                \n\
        \" <> txt0 <> "\n\
        \                                                                                \n\
        \... but the constructor is missing because the union only defines the following \n\
        \alternatives:                                                                   \n\
        \                                                                                \n\
        \" <> txt1 <> "\n"
      where
        txt0 = insert k
        txt1 = insert expr0

prettyTypeMessage (ProjectionTypeMismatch k expr0 expr1 expr2 expr3) = ErrorMessages {..}
  where
    short = "Projection type mismatch\n"
        <>  "\n"
        <>  Dhall.Diff.doc (Dhall.Diff.diffNormalized expr2 expr3)

    hints = []

    long =
        "Explanation: You can project a subset of fields from a record by specifying the \n\
        \desired type of the final record, like this:                                    \n\
        \                                                                                \n\
        \                                                                                \n\
        \    ┌─────────────────────────────────────────────┐                             \n\
        \    │ { foo = 1, bar = True }.({ foo : Natural }) │  This is valid              \n\
        \    └─────────────────────────────────────────────┘                             \n\
        \                                                                                \n\
        \                                                                                \n\
        \... but the expected type for each desired field must match the actual type of  \n\
        \the corresponding field in the original record.                                 \n\
        \                                                                                \n\
        \For example, the following expression is " <> _NOT <> " valid:                  \n\
        \                                                                                \n\
        \              Invalid: The ❰foo❱ field contains ❰1❱, which has type ❰Natural❱...\n\
        \              ⇩                                                                 \n\
        \    ┌──────────────────────────────────────────┐                                \n\
        \    │ { foo = 1, bar = True }.({ foo : Text }) │                                \n\
        \    └──────────────────────────────────────────┘                                \n\
        \                                       ⇧                                        \n\
        \                                       ... but we requested that the ❰foo❱ field\n\
        \                                       must contain a value of type ❰Text❱      \n\
        \                                                                                \n\
        \                                                                                \n\
        \You tried to project out a field named:                                         \n\
        \                                                                                \n\
        \" <> txt0 <> "\n\
        \                                                                                \n\
        \... that should have type:                                                      \n\
        \                                                                                \n\
        \" <> txt1 <> "\n\
        \                                                                                \n\
        \... but that field instead had a value of type:                                 \n\
        \                                                                                \n\
        \" <> txt2 <> "\n"
      where
        txt0 = insert k
        txt1 = insert expr0
        txt2 = insert expr1

prettyTypeMessage (AssertionFailed expr0 expr1) = ErrorMessages {..}
  where
    short = "Assertion failed\n"
        <>  "\n"
        <>  Dhall.Diff.doc (Dhall.Diff.diffNormalized expr0 expr1)

    hints = []

    long =
        "Explanation: You can assert at type-checking time that two terms are equal if   \n\
        \they have the same normal form, like this:                                      \n\
        \                                                                                \n\
        \                                                                                \n\
        \    ┌────────────────────┐                                                      \n\
        \    │ assert : 2 + 2 ≡ 4 │  This is valid                                       \n\
        \    └────────────────────┘                                                      \n\
        \                                                                                \n\
        \                                                                                \n\
        \... and an assertion still succeeds if the normal forms only differ by renaming \n\
        \bound variables, like this:                                                     \n\
        \                                                                                \n\
        \                                                                                \n\
        \    ┌──────────────────────────────────────────────────────┐                    \n\
        \    │ assert : λ(n : Natural) → n + 0 ≡ λ(m : Natural) → m │  This is also valid\n\
        \    └──────────────────────────────────────────────────────┘                    \n\
        \                                                                                \n\
        \                                                                                \n\
        \However, an assertion fails if the normal forms differ in any other way.  For   \n\
        \example, the following assertion is " <> _NOT <> " valid:                       \n\
        \                                                                                \n\
        \                                                                                \n\
        \    ┌────────────────┐                                                          \n\
        \    │ assert : 0 ≡ 1 │  Invalid: ❰0❱ does not equal ❰1❱                         \n\
        \    └────────────────┘                                                          \n\
        \                                                                                \n\
        \                                                                                \n\
        \Some common reasons why you might get this error:                               \n\
        \                                                                                \n\
        \● You might have tried to ❰assert❱ a precondition on a function's input, like   \n\
        \  this:                                                                         \n\
        \                                                                                \n\
        \                                                                                \n\
        \    ┌──────────────────────────────────────────────────────────────────┐        \n\
        \    │ λ(n : Natural) → let _ = assert : Natural/isZero n ≡ False in n  │        \n\
        \    └──────────────────────────────────────────────────────────────────┘        \n\
        \                                        ⇧                                       \n\
        \                                        Invalid: This assertion will always fail\n\
        \                                                                                \n\
        \                                                                                \n\
        \  This will not work.  Such an assertion is checking all possible inputs to the \n\
        \  function, before you've even used the function at all.                        \n\
        \                                                                                \n\
        \────────────────────────────────────────────────────────────────────────────────\n\
        \                                                                                \n\
        \You tried to assert that this expression:                                       \n\
        \                                                                                \n\
        \" <> txt0 <> "\n\
        \                                                                                \n\
        \... is the same as this other expression:                                       \n\
        \                                                                                \n\
        \" <> txt1 <> "\n\
        \                                                                                \n\
        \... but they differ\n"
      where
        txt0 = insert expr0
        txt1 = insert expr1

prettyTypeMessage (NotAnEquivalence expr) = ErrorMessages {..}
  where
    short = "Not an equivalence\n"

    hints = []

    long =
        "Explanation: The type annotation for an ❰assert❱ must evaluate to an equivalence\n\
        \of the form ❰x ≡ y❱, like this:                                                 \n\
        \                                                                                \n\
        \                                                                                \n\
        \    ┌────────────────────┐                                                      \n\
        \    │ assert : 2 + 2 ≡ 4 │  This is valid                                       \n\
        \    └────────────────────┘                                                      \n\
        \                                                                                \n\
        \                                                                                \n\
        \... but any other type is not a valid annotation.  For example, the following   \n\
        \assertion is " <> _NOT <> " valid:                                              \n\
        \                                                                                \n\
        \                                                                                \n\
        \    ┌───────────────┐                                                           \n\
        \    │ assert : True │  Invalid: ❰True❱ is not an equivalence                    \n\
        \    └───────────────┘                                                           \n\
        \                                                                                \n\
        \                                                                                \n\
        \Some common reasons why you might get this error:                               \n\
        \                                                                                \n\
        \● You tried to supply an expression of type ❰Bool❱ to the assertion, rather than\n\
        \  two separate expressions to compare, like this:                               \n\
        \                                                                                \n\
        \                                                                                \n\
        \    ┌───────────────────────────┐                                               \n\
        \    │ assert : Natural/isZero 0 │  Invalid: A boolean expression is not the     \n\
        \    └───────────────────────────┘  same thing as a type-level equivalence       \n\
        \                                                                                \n\
        \                                                                                \n\
        \  You have to explicitly compare two expressions, even if that just means       \n\
        \  comparing the expression to ❰True❱, like this:                                \n\
        \                                                                                \n\
        \                                                                                \n\
        \    ┌──────────────────────────────────┐                                        \n\
        \    │ assert : Natural/isZero 0 ≡ True │  Valid: You can assert that two boolean\n\
        \    └──────────────────────────────────┘  expressions are equivalent            \n\
        \                                                                                \n\
        \                                                                                \n\
        \────────────────────────────────────────────────────────────────────────────────\n\
        \                                                                                \n\
        \You provided the following type annotation for an ❰assert❱:                     \n\
        \                                                                                \n\
        \" <> txt0 <> "\n\
        \                                                                                \n\
        \... which is not an equivalence\n"
      where
        txt0 = insert expr

prettyTypeMessage (IncomparableExpression expr) = ErrorMessages {..}
  where
    short = "Incomparable expression\n"

    hints = []

    long =
        "Explanation: You can use an ❰assert❱ to compare two terms for equivalence, like \n\
        \this:                                                                           \n\
        \                                                                                \n\
        \                                                                                \n\
        \    ┌────────────────────┐                                                      \n\
        \    │ assert : 2 + 2 ≡ 4 │  This is valid because ❰2 + 2❱ and ❰4❱ are both terms\n\
        \    └────────────────────┘                                                      \n\
        \                                                                                \n\
        \                                                                                \n\
        \... but you cannot compare expressions, that are not terms, such as types.  For \n\
        \example, the following equivalence is " <> _NOT <> " valid:                     \n\
        \                                                                                \n\
        \                                                                                \n\
        \    ┌────────────────────────────┐                                              \n\
        \    │ assert : Natural ≡ Natural │  Invalid: ❰Natural❱ is a type, not a term    \n\
        \    └────────────────────────────┘                                              \n\
        \                                                                                \n\
        \                                                                                \n\
        \You tried to compare the following expression:                                  \n\
        \                                                                                \n\
        \" <> txt0 <> "\n\
        \                                                                                \n\
        \... which is not a term\n"
      where
        txt0 = insert expr

prettyTypeMessage (EquivalenceTypeMismatch l _L r _R) = ErrorMessages {..}
  where
    short = "The two sides of the equivalence have different types"

    hints = []

    long =
        "Explanation: You can use ❰≡❱ to compare two terms of the same type for          \n\
        \equivalence, like this:                                                         \n\
        \                                                                                \n\
        \                                                                                \n\
        \    ┌───────────┐                                                               \n\
        \    │ 2 + 2 ≡ 4 │  This is valid because ❰2 + 2❱ and ❰4❱ have the same type     \n\
        \    └───────────┘                                                               \n\
        \                                                                                \n\
        \                                                                                \n\
        \... but you cannot compare expressions, that have different types.  For example,\n\
        \the following assertion is " <> _NOT <> " valid:                                \n\
        \                                                                                \n\
        \                                                                                \n\
        \    ┌──────────┐                                                                \n\
        \    │ 1 ≡ True │  Invalid: ❰1❱ has type ❰Natural❱, ❰True❱ has type ❰Bool❱       \n\
        \    └──────────┘                                                                \n\
        \                                                                                \n\
        \                                                                                \n\
        \You tried to compare the following expressions:                                 \n\
        \                                                                                \n\
        \" <> insert l <> "\n\
        \                                                                                \n\
        \... which has type\n\
        \                                                                                \n\
        \" <> insert _L <> "\n\
        \                                                                                \n\
        \... and\n\
        \                                                                                \n\
        \" <> insert r <> "\n\
        \                                                                                \n\
        \... which has type\n\
        \                                                                                \n\
        \" <> insert _R <> "\n"

prettyTypeMessage (NotWithARecord expr0 expr1) = ErrorMessages {..}
  where
    short = "❰with❱ only works on records"

    hints = []

    long =
        "Explanation: You can use ❰with❱ to update a record, like this:                  \n\
        \                                                                                \n\
        \                                                                                \n\
        \    ┌─────────────────────────┐                                                 \n\
        \    │  { a = 5 } with b = 10  │  This is valid because ❰{ a = 5}❱ is a record   \n\
        \    └────────────────────────┘                                                  \n\
        \                                                                                \n\
        \    ┌──────────────────────────────────────────┐                                \n\
        \    │  λ(r : { a : Natural }) → r with b = 10  │  This is also valid because    \n\
        \    └──────────────────────────────────────────┘  ❰r❱ is a record               \n\
        \                                                                                \n\
        \                                                                                \n\
        \... but you cannot use ❰with❱ to update an expression that is not a record.  For\n\
        \example, the following expression is " <> _NOT <> " valid:                      \n\
        \                                                                                \n\
        \                                                                                \n\
        \    ┌───────────────┐                                                           \n\
        \    │ 1 with b = 10 │  Invalid: ❰1❱ is not a record                             \n\
        \    └───────────────┘                                                           \n\
        \                                                                                \n\
        \                                                                                \n\
        \You tried to update the following expressions:                                  \n\
        \                                                                                \n\
        \" <> txt0 <> "\n\
        \                                                                                \n\
        \... which has type\n\
        \                                                                                \n\
        \" <> txt1 <> "\n\
        \                                                                                \n\
        \... which is not a record type\n"
      where
        txt0 = insert expr0
        txt1 = insert expr1

prettyTypeMessage (CantAnd expr0 expr1) =
        buildBooleanOperator "&&" expr0 expr1

prettyTypeMessage (CantOr expr0 expr1) =
        buildBooleanOperator "||" expr0 expr1

prettyTypeMessage (CantEQ expr0 expr1) =
        buildBooleanOperator "==" expr0 expr1

prettyTypeMessage (CantNE expr0 expr1) =
        buildBooleanOperator "!=" expr0 expr1

prettyTypeMessage (CantInterpolate expr0 expr1) = ErrorMessages {..}
  where
    short = "You can only interpolate ❰Text❱"

    hints = []

    long =
        "Explanation: Text interpolation only works on expressions of type ❰Text❱        \n\
        \                                                                                \n\
        \For example, these are all valid uses of string interpolation:                  \n\
        \                                                                                \n\
        \                                                                                \n\
        \    ┌──────────────────┐                                                        \n\
        \    │ \"ABC${\"DEF\"}GHI\" │                                                        \n\
        \    └──────────────────┘                                                        \n\
        \                                                                                \n\
        \                                                                                \n\
        \    ┌────────────────────────────┐                                              \n\
        \    │ λ(x : Text) → \"ABC${x}GHI\" │                                              \n\
        \    └────────────────────────────┘                                              \n\
        \                                                                                \n\
        \                                                                                \n\
        \    ┌───────────────────────────────────────────────┐                           \n\
        \    │ λ(age : Natural) → \"Age: ${Natural/show age}\" │                           \n\
        \    └───────────────────────────────────────────────┘                           \n\
        \                                                                                \n\
        \                                                                                \n\
        \Some common reasons why you might get this error:                               \n\
        \                                                                                \n\
        \● You might have thought that string interpolation automatically converts the   \n\
        \  interpolated value to a ❰Text❱ representation of that value:                  \n\
        \                                                                                \n\
        \                                                                                \n\
        \    ┌──────────────────────────────────┐                                        \n\
        \    │ λ(age : Natural) → \"Age: ${age}\" │                                        \n\
        \    └──────────────────────────────────┘                                        \n\
        \                                  ⇧                                             \n\
        \                                  Invalid: ❰age❱ has type ❰Natural❱             \n\
        \                                                                                \n\
        \                                                                                \n\
        \● You might have forgotten to escape a string interpolation that you wanted     \n\
        \  Dhall to ignore and pass through:                                             \n\
        \                                                                                \n\
        \                                                                                \n\
        \    ┌────────────────┐                                                          \n\
        \    │ \"echo ${HOME}\" │                                                          \n\
        \    └────────────────┘                                                          \n\
        \             ⇧                                                                  \n\
        \             ❰HOME❱ is not in scope and this might have meant to use ❰\\${HOME}❱\n\
        \                                                                                \n\
        \                                                                                \n\
        \────────────────────────────────────────────────────────────────────────────────\n\
        \                                                                                \n\
        \You interpolated this expression:                                               \n\
        \                                                                                \n\
        \" <> txt0 <> "\n\
        \                                                                                \n\
        \... which does not have type ❰Text❱ but instead has type:                       \n\
        \                                                                                \n\
        \" <> txt1 <> "\n"
      where
        txt0 = insert expr0
        txt1 = insert expr1

prettyTypeMessage (CantTextAppend expr0 expr1) = ErrorMessages {..}
  where
    short = "❰++❱ only works on ❰Text❱"

    hints = []

    long =
        "Explanation: The ❰++❱ operator expects two arguments that have type ❰Text❱      \n\
        \                                                                                \n\
        \For example, this is a valid use of ❰++❱:                                       \n\
        \                                                                                \n\
        \                                                                                \n\
        \    ┌────────────────┐                                                          \n\
        \    │ \"ABC\" ++ \"DEF\" │                                                          \n\
        \    └────────────────┘                                                          \n\
        \                                                                                \n\
        \                                                                                \n\
        \Some common reasons why you might get this error:                               \n\
        \                                                                                \n\
        \● You might have thought that ❰++❱ was the operator to combine two lists:       \n\
        \                                                                                \n\
        \                                                                                \n\
        \    ┌────────────────────────┐                                                  \n\
        \    │ [1, 2, 3] ++ [4, 5, 6] │  Not valid                                       \n\
        \    └────────────────────────┘                                                  \n\
        \                                                                                \n\
        \                                                                                \n\
        \  ... but the list concatenation operator is actually ❰#❱:                      \n\
        \                                                                                \n\
        \                                                                                \n\
        \    ┌───────────────────────┐                                                   \n\
        \    │ [1, 2, 3] # [4, 5, 6] │  Valid                                            \n\
        \    └───────────────────────┘                                                   \n\
        \                                                                                \n\
        \                                                                                \n\
        \────────────────────────────────────────────────────────────────────────────────\n\
        \                                                                                \n\
        \You provided this argument:                                                     \n\
        \                                                                                \n\
        \" <> txt0 <> "\n\
        \                                                                                \n\
        \... which does not have type ❰Text❱ but instead has type:                       \n\
        \                                                                                \n\
        \" <> txt1 <> "\n"
      where
        txt0 = insert expr0
        txt1 = insert expr1

prettyTypeMessage (CantListAppend expr0 expr1) = ErrorMessages {..}
  where
    short = "❰#❱ only works on ❰List❱s"

    hints = []

    long =
        "Explanation: The ❰#❱ operator expects two arguments that are both ❰List❱s       \n\
        \                                                                                \n\
        \For example, this is a valid use of ❰#❱:                                        \n\
        \                                                                                \n\
        \                                                                                \n\
        \    ┌───────────────────────┐                                                   \n\
        \    │ [1, 2, 3] # [4, 5, 6] │                                                   \n\
        \    └───────────────────────┘                                                   \n\
        \                                                                                \n\
        \                                                                                \n\
        \────────────────────────────────────────────────────────────────────────────────\n\
        \                                                                                \n\
        \You provided this argument:                                                     \n\
        \                                                                                \n\
        \" <> txt0 <> "\n\
        \                                                                                \n\
        \... which is not a ❰List❱ but instead has type:                                 \n\
        \                                                                                \n\
        \" <> txt1 <> "\n"
      where
        txt0 = insert expr0
        txt1 = insert expr1

prettyTypeMessage (CantAdd expr0 expr1) =
        buildNaturalOperator "+" expr0 expr1

prettyTypeMessage (CantMultiply expr0 expr1) =
        buildNaturalOperator "*" expr0 expr1

buildBooleanOperator :: Pretty a => Text -> Expr s a -> Expr s a -> ErrorMessages
buildBooleanOperator operator expr0 expr1 = ErrorMessages {..}
  where
    short = "❰" <> txt2 <> "❱ only works on ❰Bool❱s"

    hints = []

    long =
        "Explanation: The ❰" <> txt2 <> "❱ operator expects two arguments that have type ❰Bool❱\n\
        \                                                                                \n\
        \For example, this is a valid use of ❰" <> txt2 <> "❱:                           \n\
        \                                                                                \n\
        \                                                                                \n\
        \    ┌───────────────┐                                                           \n\
        \    │ True " <> txt2 <> " False │                                               \n\
        \    └───────────────┘                                                           \n\
        \                                                                                \n\
        \                                                                                \n\
        \You provided this argument:                                                     \n\
        \                                                                                \n\
        \" <> txt0 <> "\n\
        \                                                                                \n\
        \... which does not have type ❰Bool❱ but instead has type:                       \n\
        \                                                                                \n\
        \" <> txt1 <> "\n"
      where
        txt0 = insert expr0
        txt1 = insert expr1

    txt2 = pretty operator

buildNaturalOperator :: Pretty a => Text -> Expr s a -> Expr s a -> ErrorMessages
buildNaturalOperator operator expr0 expr1 = ErrorMessages {..}
  where
    short = "❰" <> txt2 <> "❱ only works on ❰Natural❱s"

    hints = []

    long =
        "Explanation: The ❰" <> txt2 <> "❱ operator expects two arguments that have type ❰Natural❱\n\
        \                                                                                \n\
        \For example, this is a valid use of ❰" <> txt2 <> "❱:                           \n\
        \                                                                                \n\
        \                                                                                \n\
        \    ┌───────┐                                                                   \n\
        \    │ 3 " <> txt2 <> " 5 │                                                      \n\
        \    └───────┘                                                                   \n\
        \                                                                                \n\
        \                                                                                \n\
        \Some common reasons why you might get this error:                               \n\
        \                                                                                \n\
        \● You might have tried to use an ❰Integer❱, which is " <> _NOT <> " allowed:    \n\
        \                                                                                \n\
        \                                                                                \n\
        \    ┌─────────────────────────────────────────┐                                 \n\
        \    │ λ(x : Integer) → λ(y : Integer) → x " <> txt2 <> " y │  Not valid         \n\
        \    └─────────────────────────────────────────┘                                 \n\
        \                                                                                \n\
        \                                                                                \n\
        \  You can only use ❰Natural❱ numbers                                            \n\
        \                                                                                \n\
        \                                                                                \n\
        \● You might have mistakenly used an ❰Integer❱ literal, which is " <> _NOT <> " allowed:\n\
        \                                                                                \n\
        \                                                                                \n\
        \    ┌─────────┐                                                                 \n\
        \    │ +2 " <> txt2 <> " +2 │  Not valid                                         \n\
        \    └─────────┘                                                                 \n\
        \                                                                                \n\
        \                                                                                \n\
        \  You need to remove the leading ❰+❱ to transform them into ❰Natural❱ literals, \n\
        \  like this:                                                                    \n\
        \                                                                                \n\
        \                                                                                \n\
        \    ┌───────┐                                                                   \n\
        \    │ 2 " <> txt2 <> " 2 │  Valid                                               \n\
        \    └───────┘                                                                   \n\
        \                                                                                \n\
        \                                                                                \n\
        \────────────────────────────────────────────────────────────────────────────────\n\
        \                                                                                \n\
        \You provided this argument:                                                     \n\
        \                                                                                \n\
        \" <> txt0 <> "\n\
        \                                                                                \n\
        \... which does not have type ❰Natural❱ but instead has type:                    \n\
        \                                                                                \n\
        \" <> txt1 <> "\n"
      where
        txt0 = insert expr0
        txt1 = insert expr1

    txt2 = pretty operator

-- | A structured type error that includes context
data TypeError s a = TypeError
    { context     :: Context (Expr s a)
    , current     :: Expr s a
    , typeMessage :: TypeMessage s a
    }

instance (Eq a, Pretty s, Pretty a) => Show (TypeError s a) where
    show = Pretty.renderString . Dhall.Pretty.layout . prettyTypeError

instance (Eq a, Pretty s, Pretty a, Typeable s, Typeable a) => Exception (TypeError s a)

instance (Eq a, Pretty s, Pretty a) => Pretty (TypeError s a) where
    pretty = Pretty.unAnnotate . prettyTypeError

prettyTypeError :: (Eq a, Pretty s, Pretty a) => TypeError s a -> Doc Ann
prettyTypeError (TypeError _ expr msg) =
    (   "\n"
    <>  shortTypeMessage msg <> "\n"
    <>  source
    )
  where
    source = case expr of
        Note s _ -> pretty s
        _        -> mempty

{-| Wrap a type error in this exception type to censor source code and
    `Dhall.Syntax.Text` literals from the error message
-}
data Censored
    = CensoredDetailed (DetailedTypeError Src X)
    | Censored (TypeError Src X)

instance Show Censored where
    show = Pretty.renderString . Dhall.Pretty.layout . Pretty.pretty

instance Exception Censored

instance Pretty Censored where
    pretty (CensoredDetailed (DetailedTypeError e)) =
        pretty (DetailedTypeError (censorTypeError e))
    pretty (Censored e) = pretty (censorTypeError e)

censorTypeError :: TypeError Src a -> TypeError Src a
censorTypeError (TypeError c e m) = TypeError c' e' m'
  where
    c' = fmap Dhall.Core.censorExpression c

    e' = Dhall.Core.censorExpression e

    m' = over messageExpressions Dhall.Core.censorExpression m

-- | @Traversal@ that traverses every `Expr` in a `TypeMessage`
messageExpressions
    :: Applicative f
    => (Expr s a -> f (Expr t b)) -> TypeMessage s a -> f (TypeMessage t b)
messageExpressions f m = case m of
    UnboundVariable a ->
        UnboundVariable <$> pure a
    InvalidInputType a ->
        InvalidInputType <$> f a
    InvalidOutputType a ->
        InvalidOutputType <$> f a
    NotAFunction a b ->
        NotAFunction <$> f a <*> f b
    TypeMismatch a b c d ->
        TypeMismatch <$> f a <*> f b <*> f c <*> f d
    AnnotMismatch a b c ->
        AnnotMismatch <$> f a <*> f b <*> f c
    Untyped ->
        pure Untyped
    MissingListType ->
        pure MissingListType
    MismatchedListElements a b c d ->
        MismatchedListElements <$> pure a <*> f b <*> f c <*> f d
    InvalidListElement a b c d ->
        InvalidListElement <$> pure a <*> f b <*> f c <*> f d
    InvalidListType a ->
        InvalidListType <$> f a
    ListLitInvariant ->
        pure ListLitInvariant
    InvalidSome a b c ->
        InvalidSome <$> f a <*> f b <*> f c
    InvalidPredicate a b ->
        InvalidPredicate <$> f a <*> f b
    IfBranchMismatch a b c d ->
        IfBranchMismatch <$> f a <*> f b <*> f c <*> f d
    InvalidFieldType a b ->
        InvalidFieldType <$> pure a <*> f b
    InvalidAlternativeType a b ->
        InvalidAlternativeType <$> pure a <*> f b
    ListAppendMismatch a b ->
        ListAppendMismatch <$> f a <*> f b
    InvalidDuplicateField a b c ->
        InvalidDuplicateField a <$> f b <*> f c
    MustUpdateARecord a b c ->
        MustUpdateARecord <$> f a <*> f b <*> f c
    MustCombineARecord a b c ->
        MustCombineARecord <$> pure a <*> f b <*> f c
    InvalidRecordCompletion a l ->
        InvalidRecordCompletion a <$> f l
    CompletionSchemaMustBeARecord l r ->
        CompletionSchemaMustBeARecord <$> f l <*> f r
    CombineTypesRequiresRecordType a b ->
        CombineTypesRequiresRecordType <$> f a <*> f b
    RecordTypeMismatch a b c d ->
        RecordTypeMismatch <$> pure a <*> pure b <*> f c <*> f d
    DuplicateFieldCannotBeMerged a ->
        pure (DuplicateFieldCannotBeMerged a)
    FieldCollision a ->
        pure (FieldCollision a)
    FieldTypeCollision a ->
        pure (FieldTypeCollision a)
    MustMergeARecord a b ->
        MustMergeARecord <$> f a <*> f b
    MustMergeUnionOrOptional a b ->
        MustMergeUnionOrOptional <$> f a <*> f b
    MustMapARecord a b ->
        MustMapARecord <$> f a <*> f b
    InvalidToMapRecordKind a b ->
        InvalidToMapRecordKind <$> f a <*> f b
    HeterogenousRecordToMap a b c ->
        HeterogenousRecordToMap <$> f a <*> f b <*> f c
    InvalidToMapType a ->
        InvalidToMapType <$> f a
    MapTypeMismatch a b ->
        MapTypeMismatch <$> f a <*> f b
    MissingToMapType ->
        pure MissingToMapType
    UnusedHandler a ->
        UnusedHandler <$> pure a
    MissingHandler e a ->
        MissingHandler <$> pure e <*> pure a
    HandlerInputTypeMismatch a b c ->
        HandlerInputTypeMismatch <$> pure a <*> f b <*> f c
    DisallowedHandlerType a b c d ->
        DisallowedHandlerType <$> pure a <*> f b <*> f c <*> pure d
    HandlerOutputTypeMismatch a b c d ->
        HandlerOutputTypeMismatch <$> pure a <*> f b <*> pure c <*> f d
    InvalidHandlerOutputType a b c ->
        InvalidHandlerOutputType <$> pure a <*> f b <*> f c
    MissingMergeType ->
        pure MissingMergeType
    HandlerNotAFunction a b ->
        HandlerNotAFunction <$> pure a <*> f b
    CantAccess a b c ->
        CantAccess <$> pure a <*> f b <*> f c
    CantProject a b c ->
        CantProject <$> pure a <*> f b <*> f c
    CantProjectByExpression a ->
        CantProjectByExpression <$> f a
    DuplicateProjectionLabel a ->
        pure (DuplicateProjectionLabel a)
    MissingField a b ->
        MissingField <$> pure a <*> f b
    MissingConstructor a b ->
        MissingConstructor <$> pure a <*> f b
    ProjectionTypeMismatch a b c d e ->
        ProjectionTypeMismatch <$> pure a <*> f b <*> f c <*> f d <*> f e
    AssertionFailed a b ->
        AssertionFailed <$> f a <*> f b
    NotAnEquivalence a ->
        NotAnEquivalence <$> f a
    IncomparableExpression a ->
        IncomparableExpression <$> f a
    EquivalenceTypeMismatch a b c d ->
        EquivalenceTypeMismatch <$> f a <*> f b <*> f c <*> f d
    NotWithARecord a b ->
        NotWithARecord <$> f a <*> f b
    CantAnd a b ->
        CantAnd <$> f a <*> f b
    CantOr a b ->
        CantOr <$> f a <*> f b
    CantEQ a b ->
        CantEQ <$> f a <*> f b
    CantNE a b ->
        CantNE <$> f a <*> f b
    CantInterpolate a b ->
        CantInterpolate <$> f a <*> f b
    CantTextAppend a b ->
        CantTextAppend <$> f a <*> f b
    CantListAppend a b ->
        CantListAppend <$> f a <*> f b
    CantAdd a b ->
        CantAdd <$> f a <*> f b
    CantMultiply a b ->
        CantMultiply <$> f a <*> f b

{-| Newtype used to wrap error messages so that they render with a more
    detailed explanation of what went wrong
-}
newtype DetailedTypeError s a = DetailedTypeError (TypeError s a)
    deriving (Typeable)

instance (Eq a, Pretty s, Pretty a) => Show (DetailedTypeError s a) where
    show = Pretty.renderString . Dhall.Pretty.layout . prettyDetailedTypeError

instance (Eq a, Pretty s, Pretty a, Typeable s, Typeable a) => Exception (DetailedTypeError s a)

instance (Eq a, Pretty s, Pretty a) => Pretty (DetailedTypeError s a) where
    pretty = Pretty.unAnnotate . prettyDetailedTypeError

prettyDetailedTypeError :: (Eq a, Pretty s, Pretty a) => DetailedTypeError s a -> Doc Ann
prettyDetailedTypeError (DetailedTypeError (TypeError ctx expr msg)) =
    (   "\n"
    <>  (   if null (Dhall.Context.toList ctx)
            then ""
            else prettyContext ctx <> "\n\n"
        )
    <>  longTypeMessage msg <> "\n"
    <>  "────────────────────────────────────────────────────────────────────────────────\n"
    <>  "\n"
    <>  source
    )
  where
    prettyKV (key, val) =
        Dhall.Util.snipDoc
            (Dhall.Pretty.Internal.prettyLabel key <> " : " <> Dhall.Pretty.prettyExpr val)

    prettyContext =
            Pretty.vsep
        .   map prettyKV
        .   reverse
        .   Dhall.Context.toList

    source = case expr of
        Note s _ -> pretty s
        _        -> mempty

{-| This function verifies that a custom context is well-formed so that
    type-checking will not loop

    Note that `typeWith` already calls `checkContext` for you on the `Context`
    that you supply
-}
checkContext :: Context (Expr s X) -> Either (TypeError s X) ()
checkContext context =
    case Dhall.Context.match context of
        Nothing ->
            return ()
        Just (x, v, context') -> do
            let shiftedV       =       Dhall.Core.shift (-1) (V x 0)  v
            let shiftedContext = fmap (Dhall.Core.shift (-1) (V x 0)) context'
            _ <- typeWith shiftedContext shiftedV
            return ()

toPath :: (Functor list, Foldable list) => list Text -> Text
toPath ks =
    Text.intercalate "."
        (Foldable.toList (fmap (Dhall.Pretty.Internal.escapeLabel True) ks))

duplicateElement :: Ord a => [a] -> Maybe a
duplicateElement = go Data.Set.empty
  where
    go _ [] = Nothing
    go found (x : xs)
        | Data.Set.member x found = Just x
        | otherwise               = go (Data.Set.insert x found) xs
