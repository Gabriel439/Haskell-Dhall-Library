{-# LANGUAGE BangPatterns      #-}
{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards   #-}
{-# LANGUAGE ViewPatterns      #-}

{-# OPTIONS_GHC -fno-warn-orphans #-}

{-| This module contains logic for converting Dhall expressions to and from
    CBOR expressions which can in turn be converted to and from a binary
    representation
-}

module Dhall.Binary
    ( -- * Encoding and decoding
      encodeExpression
    , decodeExpression

      -- * Exceptions
    , DecodingFailure(..)
    ) where

import Codec.CBOR.Decoding  (Decoder, TokenType (..))
import Codec.CBOR.Encoding  (Encoding)
import Codec.Serialise      (Serialise (decode, encode))
import Control.Applicative  (empty, (<|>))
import Control.Exception    (Exception)
import Data.ByteString.Lazy (ByteString)
import Dhall.Syntax
    ( Binding (..)
    , Chunks (..)
    , Const (..)
    , DhallDouble (..)
    , Directory (..)
    , Expr (..)
    , File (..)
    , FilePrefix (..)
    , FunctionBinding (..)
    , Import (..)
    , ImportHashed (..)
    , ImportMode (..)
    , ImportType (..)
    , MultiLet (..)
    , PreferAnnotation (..)
    , RecordField (..)
    , Scheme (..)
    , URL (..)
    , Var (..)
    )

import Data.Foldable (toList)
import Data.Void     (Void, absurd)
import GHC.Float     (double2Float, float2Double)
import Numeric.Half  (fromHalf, toHalf)

import qualified Codec.CBOR.ByteArray
import qualified Codec.CBOR.Decoding   as Decoding
import qualified Codec.CBOR.Encoding   as Encoding
import qualified Codec.CBOR.Read       as Read
import qualified Codec.Serialise       as Serialise
import qualified Data.ByteArray
import qualified Data.ByteString
import qualified Data.ByteString.Lazy
import qualified Data.ByteString.Short
import qualified Data.Foldable         as Foldable
import qualified Data.List.NonEmpty    as NonEmpty
import qualified Data.Sequence
import qualified Dhall.Crypto
import qualified Dhall.Map
import qualified Dhall.Syntax          as Syntax
import qualified Text.Printf           as Printf

{-| Convert a function applied to multiple arguments to the base function and
    the list of arguments
-}
unApply :: Expr s a -> (Expr s a, [Expr s a])
unApply e₀ = (baseFunction₀, diffArguments₀ [])
  where
    ~(baseFunction₀, diffArguments₀) = go e₀

    go (App f a) = (baseFunction, diffArguments . (a :))
      where
        ~(baseFunction, diffArguments) = go f

    go (Note _ e) = go e

    go baseFunction = (baseFunction, id)

decodeExpressionInternal :: (Int -> Decoder s a) -> Decoder s (Expr t a)
decodeExpressionInternal decodeEmbed = go
  where
    go = do
        let die message = fail ("Dhall.Binary.decodeExpressionInternal: " <> message)

        tokenType₀ <- Decoding.peekTokenType

        case tokenType₀ of
            TypeUInt -> do
                !n <- fromIntegral <$> Decoding.decodeWord

                return (Var (V "_" n))

            TypeUInt64 -> do
                !n <- fromIntegral <$> Decoding.decodeWord64

                return (Var (V "_" n))

            TypeFloat16 -> do
                !n <- float2Double <$> Decoding.decodeFloat

                return (DoubleLit (DhallDouble n))

            TypeFloat32 -> do
                !n <- float2Double <$> Decoding.decodeFloat

                return (DoubleLit (DhallDouble n))

            TypeFloat64 -> do
                !n <- Decoding.decodeDouble

                return (DoubleLit (DhallDouble n))

            TypeBool -> do
                !b <- Decoding.decodeBool

                return (BoolLit b)

            TypeString -> do
                !ba <- Decoding.decodeUtf8ByteArray

                let sb = Codec.CBOR.ByteArray.toShortByteString ba

                case Data.ByteString.Short.length sb of
                    4  | sb == "Bool"              -> return Bool
                       | sb == "List"              -> return List
                       | sb == "None"              -> return None
                       | sb == "Text"              -> return Text
                       | sb == "Type"              -> return (Const Type)
                       | sb == "Kind"              -> return (Const Kind)
                       | sb == "Sort"              -> return (Const Sort)
                    6  | sb == "Double"            -> return Double
                    7  | sb == "Integer"           -> return Integer
                       | sb == "Natural"           -> return Natural
                    8  | sb == "Optional"          -> return Optional
                    9  | sb == "List/fold"         -> return ListFold
                       | sb == "List/head"         -> return ListHead
                       | sb == "List/last"         -> return ListLast
                       | sb == "Text/show"         -> return TextShow
                    10 | sb == "List/build"        -> return ListBuild
                    11 | sb == "Double/show"       -> return DoubleShow
                       | sb == "List/length"       -> return ListLength
                       | sb == "Natural/odd"       -> return NaturalOdd
                    12 | sb == "Integer/show"      -> return IntegerShow
                       | sb == "List/indexed"      -> return ListIndexed
                       | sb == "List/reverse"      -> return ListReverse
                       | sb == "Natural/even"      -> return NaturalEven
                       | sb == "Natural/fold"      -> return NaturalFold
                       | sb == "Natural/show"      -> return NaturalShow
                       | sb == "Text/replace"      -> return TextReplace
                    13 | sb == "Integer/clamp"     -> return IntegerClamp
                       | sb == "Natural/build"     -> return NaturalBuild
                    14 | sb == "Integer/negate"    -> return IntegerNegate
                       | sb == "Natural/isZero"    -> return NaturalIsZero
                    16 | sb == "Integer/toDouble"  -> return IntegerToDouble
                       | sb == "Natural/subtract"  -> return NaturalSubtract
                    17 | sb == "Natural/toInteger" -> return NaturalToInteger
                    _                              -> die ("Unrecognized built-in: " <> show sb)

            TypeListLen -> do
                len <- Decoding.decodeListLen

                case len of
                    0 -> die "Missing tag"
                    _ -> return ()

                tokenType₁ <- Decoding.peekTokenType

                case tokenType₁ of
                    TypeString -> do
                        x <- Decoding.decodeString

                        if x == "_"
                            then die "Non-standard encoding of an α-normalized variable"
                            else return ()

                        tokenType₂ <- Decoding.peekTokenType

                        case tokenType₂ of
                            TypeUInt -> do
                                !n <- fromIntegral <$> Decoding.decodeWord

                                return (Var (V x n))

                            TypeUInt64 -> do
                                !n <- fromIntegral <$> Decoding.decodeWord64

                                return (Var (V x n))

                            _ ->
                                die ("Unexpected token type for variable index: " <> show tokenType₂)

                    TypeUInt -> do
                        tag <- Decoding.decodeWord

                        case tag of
                            0 -> do
                                !f <- go

                                let loop n !acc
                                        | n <= 0    = return acc
                                        | otherwise = do
                                              !x <- go
                                              loop (n - 1) (App acc x)

                                let nArgs = len - 2

                                if nArgs <= 0
                                    then die "Non-standard encoding of a function with no arguments"
                                    else loop nArgs f

                            1 ->
                                case len of
                                    3 -> do
                                        _A <- go

                                        b <- go

                                        return (Lam mempty (Syntax.makeFunctionBinding "_" _A) b)

                                    4 -> do
                                        x <- Decoding.decodeString

                                        if x == "_"
                                            then die "Non-standard encoding of a λ expression"
                                            else return ()

                                        _A <- go

                                        b <- go

                                        return (Lam mempty (Syntax.makeFunctionBinding x _A) b)

                                    _ ->
                                        die ("Incorrect number of tokens used to encode a λ expression: " <> show len)

                            2 ->
                                case len of
                                    3 -> do
                                        _A <- go

                                        _B <- go

                                        return (Pi mempty "_" _A _B)

                                    4 -> do
                                        x <- Decoding.decodeString

                                        if x == "_"
                                            then die "Non-standard encoding of a ∀ expression"
                                            else return ()

                                        _A <- go

                                        _B <- go

                                        return (Pi mempty x _A _B)

                                    _ ->
                                        die ("Incorrect number of tokens used to encode a ∀ expression: " <> show len)

                            3 -> do
                                opcode <- Decoding.decodeWord

                                op <- case opcode of
                                    0  -> return BoolOr
                                    1  -> return BoolAnd
                                    2  -> return BoolEQ
                                    3  -> return BoolNE
                                    4  -> return NaturalPlus
                                    5  -> return NaturalTimes
                                    6  -> return TextAppend
                                    7  -> return ListAppend
                                    8  -> return (Combine mempty Nothing)
                                    9  -> return (Prefer mempty PreferFromSource)
                                    10 -> return (CombineTypes mempty)
                                    11 -> return ImportAlt
                                    12 -> return (Equivalent mempty)
                                    13 -> return RecordCompletion
                                    _  -> die ("Unrecognized operator code: " <> show opcode)

                                l <- go

                                r <- go

                                return (op l r)

                            4 ->
                                case len of
                                    2 -> do
                                        _T <- go

                                        return (ListLit (Just (App List _T)) empty)

                                    _ -> do
                                        Decoding.decodeNull

                                        xs <- Data.Sequence.replicateA (len - 2) go
                                        return (ListLit Nothing xs)

                            5 -> do
                                Decoding.decodeNull

                                t <- go

                                return (Some t)

                            6 -> do
                                t <- go

                                u <- go

                                case len of
                                    3 ->
                                        return (Merge t u Nothing)

                                    4 -> do
                                        _T <- go

                                        return (Merge t u (Just _T))

                                    _ ->
                                        die ("Incorrect number of tokens used to encode a `merge` expression: " <> show len)

                            7 -> do
                                mapLength <- Decoding.decodeMapLen

                                xTs <- replicateDecoder mapLength $ do
                                    x <- Decoding.decodeString

                                    _T <- go

                                    return (x, Syntax.makeRecordField _T)

                                return (Record (Dhall.Map.fromList xTs))

                            8 -> do
                                mapLength <- Decoding.decodeMapLen

                                xts <- replicateDecoder mapLength $ do
                                    x <- Decoding.decodeString

                                    t <- go

                                    return (x, Syntax.makeRecordField t)

                                return (RecordLit (Dhall.Map.fromList xts))

                            9 -> do
                                t <- go

                                x <- Decoding.decodeString

                                return (Field t (Syntax.makeFieldSelection x))

                            10 -> do
                                t <- go

                                xs <- case len of
                                    3 -> do
                                        tokenType₂ <- Decoding.peekTokenType

                                        case tokenType₂ of
                                            TypeListLen -> do
                                                _ <- Decoding.decodeListLen

                                                _T <- go

                                                return (Right _T)

                                            TypeString -> do
                                                x <- Decoding.decodeString
                                                return (Left [x])

                                            _ ->
                                                die ("Unexpected token type for projection: " <> show tokenType₂)

                                    _ -> do
                                        xs <- replicateDecoder (len - 2) Decoding.decodeString

                                        return (Left xs)

                                return (Project t xs)

                            11 -> do
                                mapLength <- Decoding.decodeMapLen

                                xTs <- replicateDecoder mapLength $ do
                                    x <- Decoding.decodeString

                                    tokenType₂ <- Decoding.peekTokenType

                                    mT <- case tokenType₂ of
                                        TypeNull -> do
                                            Decoding.decodeNull

                                            return Nothing

                                        _ -> do
                                            _T <- go

                                            return (Just _T)

                                    return (x, mT)

                                return (Union (Dhall.Map.fromList xTs))

                            14 -> do
                                t <- go

                                l <- go

                                r <- go

                                return (BoolIf t l r)

                            15 -> do
                                tokenType₂ <- Decoding.peekTokenType

                                case tokenType₂ of
                                    TypeUInt -> do
                                        !n <- fromIntegral <$> Decoding.decodeWord

                                        return (NaturalLit n)

                                    TypeUInt64 -> do
                                        !n <- fromIntegral <$> Decoding.decodeWord64

                                        return (NaturalLit n)

                                    TypeInteger -> do
                                        !n <- fromIntegral <$> Decoding.decodeInteger
                                        return (NaturalLit n)

                                    _ ->
                                        die ("Unexpected token type for Natural literal: " <> show tokenType₂)

                            16 -> do
                                tokenType₂ <- Decoding.peekTokenType

                                case tokenType₂ of
                                    TypeUInt -> do
                                        !n <- fromIntegral <$> Decoding.decodeWord

                                        return (IntegerLit n)

                                    TypeUInt64 -> do
                                        !n <- fromIntegral <$> Decoding.decodeWord64

                                        return (IntegerLit n)

                                    TypeNInt -> do
                                        !n <- fromIntegral <$> Decoding.decodeNegWord

                                        return (IntegerLit $! (-1 - n))

                                    TypeNInt64 -> do
                                        !n <- fromIntegral <$> Decoding.decodeNegWord64

                                        return (IntegerLit $! (-1 - n))
                                    TypeInteger -> do
                                        n <- Decoding.decodeInteger
                                        return (IntegerLit n)

                                    _ ->
                                        die ("Unexpected token type for Integer literal: " <> show tokenType₂)

                            18 -> do
                                xys <- replicateDecoder ((len - 2) `quot` 2) $ do
                                    x <- Decoding.decodeString

                                    y <- go

                                    return (x, y)

                                z <- Decoding.decodeString

                                return (TextLit (Chunks xys z))

                            19 -> do
                                t <- go

                                return (Assert t)

                            24 ->
                                fmap Embed (decodeEmbed len)

                            25 -> do
                                bindings <- replicateDecoder ((len - 2) `quot` 3) $ do
                                    x <- Decoding.decodeString

                                    tokenType₂ <- Decoding.peekTokenType

                                    mA <- case tokenType₂ of
                                        TypeNull -> do
                                            Decoding.decodeNull

                                            return Nothing

                                        _ -> do
                                            _A <- go

                                            return (Just (Nothing, _A))

                                    a <- go

                                    return (Binding Nothing x Nothing mA Nothing a)

                                b <- go

                                return (foldr Let b bindings)

                            26 -> do
                                t <- go

                                _T <- go

                                return (Annot t _T)

                            27 -> do
                                t <- go

                                mT <- case len of
                                    2 ->
                                        return Nothing

                                    3 -> do
                                        _T <- go

                                        return (Just _T)

                                    _ ->
                                        die ("Incorrect number of tokens used to encode a type annotation: " <> show len)

                                return (ToMap t mT)

                            28 -> do
                                _T <- go

                                return (ListLit (Just _T) empty)

                            29 -> do
                                l <- go

                                n <- Decoding.decodeListLen

                                ks₀ <- replicateDecoder n Decoding.decodeString

                                ks₁ <- case NonEmpty.nonEmpty ks₀ of
                                    Nothing ->
                                        die "0 field labels in decoded with expression"
                                    Just ks₁ ->
                                        return ks₁

                                r <- go

                                return (With l ks₁ r)

                            _ ->
                                die ("Unexpected tag: " <> show tag)

                    _ ->
                        die ("Unexpected tag type: " <> show tokenType₁)

            _ ->
                die ("Unexpected initial token: " <> show tokenType₀)

encodeExpressionInternal :: (a -> Encoding) -> Expr Void a -> Encoding
encodeExpressionInternal encodeEmbed = go
  where
    go e = case e of
        Var (V "_" n) ->
            Encoding.encodeInt n

        Var (V x n) ->
                Encoding.encodeListLen 2
            <>  Encoding.encodeString x
            <>  Encoding.encodeInt n

        NaturalBuild ->
            Encoding.encodeUtf8ByteArray "Natural/build"

        NaturalFold ->
            Encoding.encodeUtf8ByteArray "Natural/fold"

        NaturalIsZero ->
            Encoding.encodeUtf8ByteArray "Natural/isZero"

        NaturalEven ->
            Encoding.encodeUtf8ByteArray "Natural/even"

        NaturalOdd ->
            Encoding.encodeUtf8ByteArray "Natural/odd"

        NaturalToInteger ->
            Encoding.encodeUtf8ByteArray "Natural/toInteger"

        NaturalShow ->
            Encoding.encodeUtf8ByteArray "Natural/show"

        NaturalSubtract ->
            Encoding.encodeUtf8ByteArray "Natural/subtract"

        IntegerToDouble ->
            Encoding.encodeUtf8ByteArray "Integer/toDouble"

        IntegerClamp ->
            Encoding.encodeUtf8ByteArray "Integer/clamp"

        IntegerNegate ->
            Encoding.encodeUtf8ByteArray "Integer/negate"

        IntegerShow ->
            Encoding.encodeUtf8ByteArray "Integer/show"

        DoubleShow ->
            Encoding.encodeUtf8ByteArray "Double/show"

        ListBuild ->
            Encoding.encodeUtf8ByteArray "List/build"

        ListFold ->
            Encoding.encodeUtf8ByteArray "List/fold"

        ListLength ->
            Encoding.encodeUtf8ByteArray "List/length"

        ListHead ->
            Encoding.encodeUtf8ByteArray "List/head"

        ListLast ->
            Encoding.encodeUtf8ByteArray "List/last"

        ListIndexed ->
            Encoding.encodeUtf8ByteArray "List/indexed"

        ListReverse ->
            Encoding.encodeUtf8ByteArray "List/reverse"

        Bool ->
            Encoding.encodeUtf8ByteArray "Bool"

        Optional ->
            Encoding.encodeUtf8ByteArray "Optional"

        None ->
            Encoding.encodeUtf8ByteArray "None"

        Natural ->
            Encoding.encodeUtf8ByteArray "Natural"

        Integer ->
            Encoding.encodeUtf8ByteArray "Integer"

        Double ->
            Encoding.encodeUtf8ByteArray "Double"

        Text ->
            Encoding.encodeUtf8ByteArray "Text"

        TextReplace ->
            Encoding.encodeUtf8ByteArray "Text/replace"

        TextShow ->
            Encoding.encodeUtf8ByteArray "Text/show"

        List ->
            Encoding.encodeUtf8ByteArray "List"

        Const Type ->
            Encoding.encodeUtf8ByteArray "Type"

        Const Kind ->
            Encoding.encodeUtf8ByteArray "Kind"

        Const Sort ->
            Encoding.encodeUtf8ByteArray "Sort"

        a@App{} ->
            encodeListN
                (2 + length arguments)
                ( Encoding.encodeInt 0
                : go function
                : map go arguments
                )
          where
            (function, arguments) = unApply a

        Lam _ (FunctionBinding { functionBindingVariable = "_", functionBindingAnnotation = _A }) b ->
            encodeList3
                (Encoding.encodeInt 1)
                (go _A)
                (go b)

        Lam _ (FunctionBinding { functionBindingVariable = x, functionBindingAnnotation = _A }) b ->
            encodeList4
                (Encoding.encodeInt 1)
                (Encoding.encodeString x)
                (go _A)
                (go b)

        Pi _ "_" _A _B ->
            encodeList3
                (Encoding.encodeInt 2)
                (go _A)
                (go _B)

        Pi _ x _A _B ->
            encodeList4
                (Encoding.encodeInt 2)
                (Encoding.encodeString x)
                (go _A)
                (go _B)

        BoolOr l r ->
            encodeOperator 0 l r

        BoolAnd l r ->
            encodeOperator 1 l r

        BoolEQ l r ->
            encodeOperator 2 l r

        BoolNE l r ->
            encodeOperator 3 l r

        NaturalPlus l r ->
            encodeOperator 4 l r

        NaturalTimes l r ->
            encodeOperator 5 l r

        TextAppend l r ->
            encodeOperator 6 l r

        ListAppend l r ->
            encodeOperator 7 l r

        Combine _ _ l r ->
            encodeOperator 8 l r

        Prefer _ _ l r ->
            encodeOperator 9 l r

        CombineTypes _ l r ->
            encodeOperator 10 l r

        ImportAlt l r ->
            encodeOperator 11 l r

        Equivalent _ l r ->
            encodeOperator 12 l r

        RecordCompletion l r ->
            encodeOperator 13 l r

        ListLit _T₀ xs
            | null xs ->
                encodeList2 (Encoding.encodeInt label) _T₁
            | otherwise ->
                encodeListN
                    (2 + length xs)
                    ( Encoding.encodeInt 4
                    : Encoding.encodeNull
                    : map go (Data.Foldable.toList xs)
                    )
          where
            (label, _T₁) = case _T₀ of
                Nothing           -> (4 , Encoding.encodeNull)
                Just (App List t) -> (4 , go t               )
                Just  t           -> (28, go t               )

        Some t ->
            encodeList3
                (Encoding.encodeInt 5)
                Encoding.encodeNull
                (go t)

        Merge t u Nothing ->
            encodeList3
                (Encoding.encodeInt 6)
                (go t)
                (go u)

        Merge t u (Just _T) ->
            encodeList4
                (Encoding.encodeInt 6)
                (go t)
                (go u)
                (go _T)

        Record xTs ->
            encodeList2
                (Encoding.encodeInt 7)
                (encodeMapWith (go . recordFieldValue) xTs)

        RecordLit xts ->
            encodeList2
                (Encoding.encodeInt 8)
                (encodeMapWith (go. recordFieldValue) xts)

        Field t (Syntax.fieldSelectionLabel -> x) ->
            encodeList3
                (Encoding.encodeInt 9)
                (go t)
                (Encoding.encodeString x)

        Project t (Left xs) ->
            encodeListN
                (2 + length xs)
                ( Encoding.encodeInt 10
                : go t
                : map Encoding.encodeString xs
                )

        Project t (Right _T) ->
            encodeList3
                (Encoding.encodeInt 10)
                (go t)
                (encodeList1 (go _T))

        Union xTs ->
            encodeList2
                (Encoding.encodeInt 11)
                (encodeMapWith encodeValue xTs)
          where
            encodeValue  Nothing  = Encoding.encodeNull
            encodeValue (Just _T) = go _T

        BoolLit b ->
            Encoding.encodeBool b

        BoolIf t l r ->
            encodeList4
                (Encoding.encodeInt 14)
                (go t)
                (go l)
                (go r)

        NaturalLit n ->
            encodeList2
                (Encoding.encodeInt 15)
                (Encoding.encodeInteger (fromIntegral n))

        IntegerLit n ->
            encodeList2
                (Encoding.encodeInt 16)
                (Encoding.encodeInteger (fromIntegral n))

        DoubleLit (DhallDouble n64)
            | useHalf   -> Encoding.encodeFloat16 n32
            | useFloat  -> Encoding.encodeFloat n32
            | otherwise -> Encoding.encodeDouble n64
          where
            n32 = double2Float n64

            n16 = toHalf n32

            useFloat = n64 == float2Double n32

            useHalf = n64 == (float2Double $ fromHalf n16)

        -- Fast path for the common case of an uninterpolated string
        TextLit (Chunks [] z) ->
            encodeList2
                (Encoding.encodeInt 18)
                (Encoding.encodeString z)

        TextLit (Chunks xys z) ->
            encodeListN
                (2 + 2 * length xys)
                ( Encoding.encodeInt 18
                : concatMap encodePair xys ++ [ Encoding.encodeString z ]
                )
          where
            encodePair (x, y) = [ Encoding.encodeString x, go y ]

        Assert t ->
            encodeList2
                (Encoding.encodeInt 19)
                (go t)

        Embed x ->
            encodeEmbed x

        Let a₀ b₀ ->
            encodeListN
                (2 + 3 * length as)
                ( Encoding.encodeInt 25
                : concatMap encodeBinding (toList as) ++ [ go b₁ ]
                )
          where
            MultiLet as b₁ = Syntax.multiLet a₀ b₀

            encodeBinding (Binding _ x _ mA₀ _ a) =
                [ Encoding.encodeString x
                , mA₁
                , go a
                ]
              where
                mA₁ = case mA₀ of
                    Nothing      -> Encoding.encodeNull
                    Just (_, _A) -> go _A

        Annot t _T ->
            encodeList3
                (Encoding.encodeInt 26)
                (go t)
                (go _T)

        ToMap t Nothing ->
            encodeList2
                (Encoding.encodeInt 27)
                (go t)

        ToMap t (Just _T) ->
            encodeList3
                (Encoding.encodeInt 27)
                (go t)
                (go _T)

        With l ks r ->
            encodeList4
                (Encoding.encodeInt 29)
                (go l)
                (encodeList (fmap Encoding.encodeString ks))
                (go r)
        HashOf t -> encodeList2 (Encoding.encodeInt 30) (go t)

        Note _ b ->
            go b

    encodeOperator n l r =
        encodeList4
            (Encoding.encodeInt 3)
            (Encoding.encodeInt n)
            (go l)
            (go r)

    encodeMapWith encodeValue m =
            Encoding.encodeMapLen (fromIntegral (Dhall.Map.size m))
        <>  foldMap encodeKeyValue (Dhall.Map.toList (Dhall.Map.sort m))
      where
        encodeKeyValue (k, v) = Encoding.encodeString k <> encodeValue v

encodeList1 :: Encoding -> Encoding
encodeList1 a = Encoding.encodeListLen 1 <> a
{-# INLINE encodeList1 #-}

encodeList2 :: Encoding -> Encoding -> Encoding
encodeList2 a b = Encoding.encodeListLen 2 <> a <> b
{-# INLINE encodeList2 #-}

encodeList3 :: Encoding -> Encoding -> Encoding -> Encoding
encodeList3 a b c = Encoding.encodeListLen 3 <> a <> b <> c
{-# INLINE encodeList3 #-}

encodeList4 :: Encoding -> Encoding -> Encoding -> Encoding -> Encoding
encodeList4 a b c d = Encoding.encodeListLen 4 <> a <> b <> c <> d
{-# INLINE encodeList4 #-}

encodeListN :: Foldable f => Int -> f Encoding -> Encoding
encodeListN len xs =
    Encoding.encodeListLen (fromIntegral len) <> Foldable.fold xs
{-# INLINE encodeListN #-}

encodeList :: Foldable f => f Encoding -> Encoding
encodeList xs = encodeListN (length xs) xs
{-# INLINE encodeList #-}

decodeImport :: Int -> Decoder s Import
decodeImport len = do
    let die message = fail ("Dhall.Binary.decodeImport: " <> message)

    tokenType₀ <- Decoding.peekTokenType

    hash <- case tokenType₀ of
        TypeNull -> do
            Decoding.decodeNull

            return Nothing

        TypeBytes -> do
            bytes <- Decoding.decodeBytes

            let (prefix, suffix) = Data.ByteString.splitAt 2 bytes

            case prefix of
                "\x12\x20" -> return ()
                _          -> die ("Unrecognized multihash prefix: " <> show prefix)
            case Dhall.Crypto.sha256DigestFromByteString suffix of
                Nothing     -> die ("Invalid sha256 digest: " <> show bytes)
                Just digest -> return (Just digest)

        _ ->
            die ("Unexpected hash token: " <> show tokenType₀)

    m <- Decoding.decodeWord

    importMode <- case m of
        0 -> return Code
        1 -> return RawText
        2 -> return Location
        _ -> die ("Unexpected code for import mode: " <> show m)

    let remote scheme = do
            tokenType₁ <- Decoding.peekTokenType

            headers <- case tokenType₁ of
                TypeNull -> do
                    Decoding.decodeNull
                    return Nothing

                _ -> do
                    headers <- decodeExpressionInternal decodeImport

                    return (Just headers)

            authority <- Decoding.decodeString

            paths <- replicateDecoder (len - 8) Decoding.decodeString

            file <- Decoding.decodeString

            tokenType₂ <- Decoding.peekTokenType

            query <- case tokenType₂ of
                TypeNull -> do
                    Decoding.decodeNull
                    return Nothing
                _ ->
                    fmap Just Decoding.decodeString

            let components = reverse paths
            let directory  = Directory {..}
            let path       = File {..}

            return (Remote (URL {..}))

    let local prefix = do
            paths <- replicateDecoder (len - 5) Decoding.decodeString

            file <- Decoding.decodeString

            let components = reverse paths
            let directory  = Directory {..}

            return (Local prefix (File {..}))

    let missing = return Missing

    let env = do
            x <- Decoding.decodeString

            return (Env x)

    n <- Decoding.decodeWord

    importType <- case n of
        0 -> remote HTTP
        1 -> remote HTTPS
        2 -> local Absolute
        3 -> local Here
        4 -> local Parent
        5 -> local Home
        6 -> env
        7 -> missing
        _ -> fail ("Unrecognized import type code: " <> show n)

    let importHashed = ImportHashed {..}

    return (Import {..})

encodeImport :: Import -> Encoding
encodeImport import_ =
    case importType of
        Remote (URL { scheme = scheme₀, .. }) ->
            encodeList
                (   prefix
                ++  [ Encoding.encodeInt scheme₁
                    , using
                    , Encoding.encodeString authority
                    ]
                ++  map Encoding.encodeString (reverse components)
                ++  [ Encoding.encodeString file ]
                ++  [ case query of
                         Nothing -> Encoding.encodeNull
                         Just q  -> Encoding.encodeString q
                    ]
                )
          where
            using = case headers of
                Nothing ->
                    Encoding.encodeNull
                Just h ->
                    encodeExpressionInternal encodeImport (Syntax.denote h)

            scheme₁ = case scheme₀ of
                HTTP  -> 0
                HTTPS -> 1

            File{..} = path

            Directory {..} = directory

        Local prefix₀ path ->
            encodeList
                (   prefix
                ++  [ Encoding.encodeInt prefix₁ ]
                ++  map Encoding.encodeString components₁
                ++  [ Encoding.encodeString file ]
                )
          where
            File{..} = path

            Directory{..} = directory

            prefix₁ = case prefix₀ of
                Absolute -> 2
                Here     -> 3
                Parent   -> 4
                Home     -> 5

            components₁ = reverse components

        Env x ->
            encodeList
                (prefix ++ [ Encoding.encodeInt 6, Encoding.encodeString x ])

        Missing ->
            encodeList (prefix ++ [ Encoding.encodeInt 7 ])
  where
    prefix = [ Encoding.encodeInt 24, h, m ]
      where
        h = case hash of
            Nothing ->
                Encoding.encodeNull

            Just digest ->
                Encoding.encodeBytes ("\x12\x20" <> Data.ByteArray.convert digest)

        m = Encoding.encodeInt (case importMode of Code -> 0; RawText -> 1; Location -> 2;)

    Import{..} = import_

    ImportHashed{..} = importHashed

decodeVoid :: Int -> Decoder s Void
decodeVoid _ = fail "Dhall.Binary.decodeVoid: Cannot decode an uninhabited type"

encodeVoid :: Void -> Encoding
encodeVoid = absurd

instance Serialise (Expr Void Void) where
    encode = encodeExpressionInternal encodeVoid

    decode = decodeExpressionInternal decodeVoid

instance Serialise (Expr Void Import) where
    encode = encodeExpressionInternal encodeImport

    decode = decodeExpressionInternal decodeImport

-- | Encode a Dhall expression as a CBOR-encoded `ByteString`
encodeExpression :: Serialise (Expr Void a) => Expr Void a -> ByteString
encodeExpression = Serialise.serialise

-- | Decode a Dhall expression from a CBOR `Codec.CBOR.Term.Term`
decodeExpression
    :: Serialise (Expr s a) => ByteString -> Either DecodingFailure (Expr s a)
decodeExpression bytes =
    case decodeWithoutVersion <|> decodeWithVersion of
        Just expression -> Right expression
        Nothing         -> Left (CBORIsNotDhall bytes)
  where
    adapt (Right ("", x)) = Just x
    adapt  _              = Nothing

    decode' = decodeWith55799Tag decode

    -- This is the behavior specified by the standard
    decodeWithoutVersion = adapt (Read.deserialiseFromBytes decode' bytes)

    -- tag to ease the migration
    decodeWithVersion = adapt (Read.deserialiseFromBytes decodeWithTag bytes)
      where
        decodeWithTag = do
            2 <- Decoding.decodeListLen

            version <- Decoding.decodeString


            -- "_" has never been a valid version string, and this ensures that
            -- we don't interpret `[ "_", 0 ]` as the expression `_` (encoded as
            -- `0`) tagged with a version string of `"_"`
            if (version == "_")
                then fail "Dhall.Binary.decodeExpression: \"_\" is not a valid version string"
                else return ()

            decode'

decodeWith55799Tag :: Decoder s a -> Decoder s a
decodeWith55799Tag decoder = do
    tokenType <- Decoding.peekTokenType

    case tokenType of
        TypeTag -> do
            w <- Decoding.decodeTag

            if w /= 55799
                then fail ("Dhall.Binary.decodeWith55799Tag: Unexpected tag: " <> show w)
                else return ()

            decoder
        _ ->
            decoder

{-| This indicates that a given CBOR-encoded `ByteString` did not correspond to
    a valid Dhall expression
-}
newtype DecodingFailure = CBORIsNotDhall ByteString
    deriving (Eq)

instance Exception DecodingFailure

_ERROR :: String
_ERROR = "\ESC[1;31mError\ESC[0m"

instance Show DecodingFailure where
    show (CBORIsNotDhall bytes) =
            _ERROR <> ": Cannot decode CBOR to Dhall\n"
        <>  "\n"
        <>  "The following bytes do not encode a valid Dhall expression\n"
        <>  "\n"
        <>  "↳ 0x" <> concatMap toHex (Data.ByteString.Lazy.unpack bytes) <> "\n"
      where
        toHex = Printf.printf "%02x "

-- | This specialized version of 'Control.Monad.replicateM' reduces
-- decoding timings by roughly 10%.
replicateDecoder :: Int -> Decoder s a -> Decoder s [a]
replicateDecoder n0 decoder = go n0
  where
    go n
      | n <= 0    = pure []
      | otherwise = do
            x <- decoder
            xs <- go (n - 1)
            pure (x:xs)
