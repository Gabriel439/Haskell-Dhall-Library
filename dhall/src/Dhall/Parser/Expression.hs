{-# LANGUAGE NamedFieldPuns      #-}
{-# LANGUAGE OverloadedLists     #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE RecordWildCards     #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- | Parsing Dhall expressions.
module Dhall.Parser.Expression where

import Control.Applicative     (Alternative (..), liftA2, optional)
import Data.ByteArray.Encoding (Base (..))
import Data.Foldable           (foldl')
import Data.List.NonEmpty      (NonEmpty (..))
import Data.Text               (Text)
import Dhall.Src               (Src (..))
import Dhall.Syntax
import Text.Parser.Combinators (choice, try, (<?>))

import qualified Control.Monad
import qualified Control.Monad.Combinators          as Combinators
import qualified Control.Monad.Combinators.NonEmpty as Combinators.NonEmpty
import qualified Data.ByteArray.Encoding
import qualified Data.ByteString
import qualified Data.Char                          as Char
import qualified Data.List
import qualified Data.List.NonEmpty                 as NonEmpty
import qualified Data.Sequence
import qualified Data.Text
import qualified Data.Text.Encoding
import qualified Data.Time                          as Time
import qualified Dhall.Crypto
import qualified Text.Megaparsec

import Dhall.Parser.Combinators
import Dhall.Parser.Token

-- | Get the current source offset (in tokens)
getOffset :: Text.Megaparsec.MonadParsec e s m => m Int
getOffset = Text.Megaparsec.stateOffset <$> Text.Megaparsec.getParserState
{-# INLINE getOffset #-}

-- | Set the current source offset
setOffset :: Text.Megaparsec.MonadParsec e s m => Int -> m ()
setOffset o = Text.Megaparsec.updateParserState $ \state ->
    state
        { Text.Megaparsec.stateOffset = o }
{-# INLINE setOffset #-}

{-| Wrap a `Parser` to still match the same text but return only the `Src`
    span
-}
src :: Parser a -> Parser Src
src parser = do
    before      <- Text.Megaparsec.getSourcePos
    (tokens, _) <- Text.Megaparsec.match parser
    after       <- Text.Megaparsec.getSourcePos
    return (Src before after tokens)

-- | Same as `src`, except also return the parsed value
srcAnd :: Parser a -> Parser (Src, a)
srcAnd parser = do
    before      <- Text.Megaparsec.getSourcePos
    (tokens, x) <- Text.Megaparsec.match parser
    after       <- Text.Megaparsec.getSourcePos
    return (Src before after tokens, x)

{-| Wrap a `Parser` to still match the same text, but to wrap the resulting
    `Expr` in a `Note` constructor containing the `Src` span
-}
noted :: Parser (Expr Src a) -> Parser (Expr Src a)
noted parser = do
    before      <- Text.Megaparsec.getSourcePos
    (tokens, e) <- Text.Megaparsec.match parser
    after       <- Text.Megaparsec.getSourcePos
    let src₀ = Src before after tokens
    case e of
        Note src₁ _ | laxSrcEq src₀ src₁ -> return e
        _                                -> return (Note src₀ e)

{-| Parse a complete expression (with leading and trailing whitespace)

    This corresponds to the @complete-expression@ rule from the official
    grammar
-}
completeExpression :: Parser a -> Parser (Expr Src a)
completeExpression embedded = completeExpression_
  where
    Parsers {..} = parsers embedded

{-| Parse an \"import expression\"

    This is not the same thing as @`fmap` `Embed`@.  This parses any
    expression of the same or higher precedence as an import expression (such
    as a selector expression).  For example, this parses @(1)@

    This corresponds to the @import-expression@ rule from the official grammar
-}
importExpression :: Parser a -> Parser (Expr Src a)
importExpression embedded = importExpression_
  where
    Parsers {..} = parsers embedded

{-| For efficiency (and simplicity) we only expose two parsers from the
    result of the `parsers` function, since these are the only parsers needed
    outside of this module
-}
data Parsers a = Parsers
    { completeExpression_ :: Parser (Expr Src a)
    , importExpression_   :: Parser (Expr Src a)
    }

{-| Parse a numeric `TimeZone`

    This corresponds to the @time-numoffset@ rule from the official grammar
-}
timeNumOffset :: Parser (Expr s a)
timeNumOffset = do
    s <- signPrefix

    hour <- timeHour

    _ <- text ":"

    minute <- timeMinute

    let minutes = s (hour * 60 + minute)

    return (TimeZoneLiteral (Time.TimeZone minutes Prelude.False ""))

{-| Parse a numeric `TimeZone` or a @Z@

    This corresponds to the @time-offset@ rule from the official grammar
-}
timeOffset :: Parser (Expr s a)
timeOffset =
        (do _ <- text "Z"

            return (TimeZoneLiteral (Time.TimeZone 0 Prelude.False ""))
        )
    <|> timeNumOffset

{-| Parse a `Time`

    This corresponds to the @partial-time@ rule from the official grammar
-}
partialTime :: Parser (Expr s a)
partialTime = do
    hour <- timeHour

    _ <- text ":"

    minute <- timeMinute

    _ <- text ":"

    second <- timeSecond

    (fraction, precision) <- timeSecFrac <|> pure (0, 0)

    let time = Time.TimeOfDay hour minute (second + fraction)

    return (TimeLiteral time precision)

{-| Parse a `Date`

    This corresponds to the @full-date@ rule from the official grammar
-}
fullDate :: Parser (Expr s a)
fullDate = do
    year <- dateFullYear

    _ <- text "-"

    month <- dateMonth

    _ <- text "-"

    day <- dateMday

    case Time.fromGregorianValid year month day of
        Nothing -> fail "Invalid calendar day"
        Just d  -> return (DateLiteral d)

{-| Parse a `Date`, `Time`, `TimeZone` or any valid permutation of them as a
    record

    This corresponds to the @temporal-literal@ rule from the official grammar
-}
temporalLiteral :: Parser (Expr s a)
temporalLiteral =
        try (do
            date <- fullDate

            _ <- text "T" <|> text "t"

            time <- partialTime

            timeZone <- timeOffset

            return
                (RecordLit
                    [   ("date"    , makeRecordField date)
                    ,   ("time"    , makeRecordField time)
                    ,   ("timeZone", makeRecordField timeZone)
                    ]
                )
        )
    <|> try (do
            date <- fullDate

            _ <- text "T" <|> text "t"

            time <- partialTime

            return
                (RecordLit
                    [   ("date", makeRecordField date)
                    ,   ("time", makeRecordField time)
                    ]
                )
        )
    <|> try (do
            time <- partialTime

            timeZone <- timeOffset

            return
                (RecordLit
                    [   ("time"    , makeRecordField time)
                    ,   ("timeZone", makeRecordField timeZone)
                    ]
                )
        )
    <|> try fullDate
    <|> try partialTime
    <|> try timeNumOffset

-- | Given a parser for imports,
parsers :: forall a. Parser a -> Parsers a
parsers embedded = Parsers {..}
  where
    completeExpression_ =
        many shebang *> whitespace *> expression <* whitespace

    shebang = do
        _ <- text "#!"

        let predicate c = ('\x20' <= c && c <= '\x10FFFF') || c == '\t'

        _ <- Dhall.Parser.Combinators.takeWhile predicate

        endOfLine

    expression =
        noted
            ( choice
                [ alternative0
                , alternative1
                , alternative2
                , alternative3
                , alternative4
                , alternative5
                ]
            ) <?> "expression"
      where
        alternative0 = do
            cs <- _lambda
            whitespace
            _openParens
            src0 <- src whitespace
            a <- label
            src1 <- src whitespace
            _colon
            src2 <- src nonemptyWhitespace
            b <- expression
            whitespace
            _closeParens
            whitespace
            cs' <- _arrow
            whitespace
            c <- expression
            return (Lam (Just (cs <> cs')) (FunctionBinding (Just src0) a (Just src1) (Just src2) b) c)

        alternative1 = do
            try (_if *> nonemptyWhitespace)
            a <- expression
            whitespace
            try (_then *> nonemptyWhitespace)
            b <- expression
            whitespace
            try (_else *> nonemptyWhitespace)
            c <- expression
            return (BoolIf a b c)

        alternative2 = do
            let binding = do
                    src0 <- try (_let *> src nonemptyWhitespace)

                    c <- label

                    src1 <- src whitespace

                    d <- optional (do
                        _colon

                        src2 <- src nonemptyWhitespace

                        e <- expression

                        whitespace

                        return (Just src2, e) )

                    _equal

                    src3 <- src whitespace

                    f <- expression

                    whitespace

                    return (Binding (Just src0) c (Just src1) d (Just src3) f)

            as <- NonEmpty.some1 binding

            try (_in *> nonemptyWhitespace)

            b <- expression

            -- 'Note's in let-in-let:
            --
            -- Subsequent @let@s that are not separated by an @in@ only get a
            -- single surrounding 'Note'. For example:
            --
            -- let x = a
            -- let y = b
            -- in  let z = c
            --     in x
            --
            -- is parsed as
            --
            -- (Note …
            --   (Let x …
            --     (Let y …
            --       (Note …
            --         (Let z …
            return (Dhall.Syntax.wrapInLets as b)

        alternative3 = do
            cs <- try (_forall <* whitespace <* _openParens)
            whitespace
            a <- label
            whitespace
            _colon
            nonemptyWhitespace
            b <- expression
            whitespace
            _closeParens
            whitespace
            cs' <- _arrow
            whitespace
            c <- expression
            return (Pi (Just (cs <> cs')) a b c)

        alternative4 = do
            try (_assert *> whitespace *> _colon)
            nonemptyWhitespace
            a <- expression
            return (Assert a)

        alternative5 = do
            (a0Info, a0) <- applicationExpressionWithInfo

            let (parseFirstOperatorExpression, parseOperatorExpression) =
                    operatorExpression (pure a0)

            let alternative5A = do
                    case a0Info of
                        ImportExpr -> return ()
                        _          -> empty

                    bs <- some (do
                        try (nonemptyWhitespace *> _with *> nonemptyWhitespace)

                        keys <- Combinators.NonEmpty.sepBy1 anyLabel (try (whitespace *> _dot) *> whitespace)

                        whitespace

                        _equal

                        whitespace

                        value <- parseOperatorExpression

                        return (\e -> With e keys value) )

                    return (foldl (\e f -> f e) a0 bs)

            let alternative5B = do
                    a <- parseFirstOperatorExpression

                    whitespace

                    let alternative5B0 = do
                            cs <- _arrow
                            whitespace
                            b <- expression
                            whitespace
                            return (Pi (Just cs) "_" a b)

                    let alternative5B1 = do
                            _colon
                            nonemptyWhitespace
                            case (shallowDenote a, a0Info) of
                                (ListLit Nothing [], _) -> do
                                    b <- applicationExpression

                                    return (ListLit (Just b) [])
                                (Merge c d Nothing, NakedMergeOrSomeOrToMap) -> do
                                    b <- applicationExpression

                                    return (Merge c d (Just b))
                                (ToMap c Nothing, NakedMergeOrSomeOrToMap) -> do
                                    b <- applicationExpression

                                    return (ToMap c (Just b))
                                _ -> do
                                    b <- expression

                                    return (Annot a b)

                    let alternative5B2 =
                            case shallowDenote a of
                                ListLit Nothing [] ->
                                    fail "Empty list literal without annotation"
                                _ -> pure a

                    alternative5B0 <|> alternative5B1 <|> alternative5B2

            alternative5A <|> alternative5B

    -- The firstApplicationExpression argument is necessary in order to
    -- left-factor the parsers for function types and @with@ expressions to
    -- minimize backtracking
    --
    -- For a longer explanation, see:
    --
    -- https://github.com/dhall-lang/dhall-haskell/pull/1770#discussion_r419022486
    operatorExpression firstApplicationExpression =
        foldr cons nil operatorParsers
      where
        cons operatorParser (p0, p) =
            ( makeOperatorExpression p0 operatorParser p
            , makeOperatorExpression p  operatorParser p
            )

        nil = (firstApplicationExpression, applicationExpression)

    makeOperatorExpression firstSubExpression operatorParser subExpression = do
            a <- firstSubExpression

            bs <- Text.Megaparsec.many $ do
                (Src _ _ textOp, op0) <- srcAnd (try (whitespace *> operatorParser))

                r0 <- subExpression

                let l@(Note (Src startL _ textL) _) `op` r@(Note (Src _ endR textR) _) =
                        Note (Src startL endR (textL <> textOp <> textR)) (l `op0` r)
                    -- We shouldn't hit this branch if things are working, but
                    -- that is not enforced in the types
                    l `op` r =
                        l `op0` r

                return (`op` r0)

            return (foldl' (\x f -> f x) a bs)

    operatorParsers :: [Parser (Expr s a -> Expr s a -> Expr s a)]
    operatorParsers =
        [ Equivalent . Just           <$> _equivalent   <* whitespace
        , ImportAlt                   <$ _importAlt     <* nonemptyWhitespace
        , BoolOr                      <$ _or            <* whitespace
        , NaturalPlus                 <$ _plus          <* nonemptyWhitespace
        , TextAppend                  <$ _textAppend    <* whitespace
        , ListAppend                  <$ _listAppend    <* whitespace
        , BoolAnd                     <$ _and           <* whitespace
        , (\cs -> Combine (Just cs) Nothing)         <$> _combine <* whitespace
        , (\cs -> Prefer (Just cs) PreferFromSource) <$> _prefer  <* whitespace
        , CombineTypes . Just         <$> _combineTypes <* whitespace
        , NaturalTimes                <$ _times         <* whitespace
        -- Make sure that `==` is not actually the prefix of `===`
        , BoolEQ                      <$ try (_doubleEqual <* Text.Megaparsec.notFollowedBy (char '=')) <* whitespace
        , BoolNE                      <$ _notEqual      <* whitespace
        ]

    applicationExpression = snd <$> applicationExpressionWithInfo

    applicationExpressionWithInfo :: Parser (ApplicationExprInfo, Expr Src a)
    applicationExpressionWithInfo = do
            let alternative0 = do
                    try (_merge *> nonemptyWhitespace)

                    a <- importExpression_ <* nonemptyWhitespace

                    return (\b -> Merge a b Nothing, Just "second argument to ❰merge❱")

            let alternative1 = do
                    try (_Some *> nonemptyWhitespace)

                    return (Some, Just "argument to ❰Some❱")

            let alternative2 = do
                    try (_toMap *> nonemptyWhitespace)

                    return (\a -> ToMap a Nothing, Just "argument to ❰toMap❱")

            let alternative3 =
                    return (id, Nothing)

            (f, maybeMessage) <- alternative0 <|> alternative1 <|> alternative2 <|> alternative3

            let adapt parser =
                    case maybeMessage of
                        Nothing      -> parser
                        Just message -> parser <?> message

            a <- adapt (noted importExpression_)

            bs <- Text.Megaparsec.many . try $ do
                (sep, _) <- Text.Megaparsec.match nonemptyWhitespace
                b <- importExpression_
                return (sep, b)

            let c = foldl' app (f a) bs

            let info =
                    case (maybeMessage, bs) of
                        (Just _ , []) -> NakedMergeOrSomeOrToMap
                        (Nothing, []) -> ImportExpr
                        _             -> ApplicationExpr

            return (info, c)
          where
            app a (sep, b)
                | Note (Src left _ bytesL) _ <- a
                , Note (Src _ right bytesR) _ <- b
                = Note (Src left right (bytesL <> sep <> bytesR)) (App a b)
            app a (_, b) =
                App a b

    importExpression_ = noted (choice [ alternative0, alternative1 ])
          where
            alternative0 = do
                a <- embedded
                return (Embed a)

            alternative1 = completionExpression

    completionExpression = noted (do
        a <- selectorExpression

        mb <- optional (do
            try (whitespace *> _doubleColon)

            whitespace

            selectorExpression )

        case mb of
            Nothing -> return a
            Just b  -> return (RecordCompletion a b) )

    selectorExpression = noted (do
            a <- primitiveExpression

            let recordType = _openParens *> whitespace *> expression <* whitespace <* _closeParens

            let field               x  e = Field   e  x
            let projectBySet        xs e = Project e (Left  xs)
            let projectByExpression xs e = Project e (Right xs)

            let alternatives = do
                    src0 <- src whitespace

                    let fieldSelection = do
                            l <- anyLabel

                            pos <- Text.Megaparsec.getSourcePos

                            -- FIXME: Suffix whitespace can't be parsed given our limitation
                            -- about whitespace treatment, but for @dhall-docs@ this
                            -- is enough
                            let src1 = Src pos pos ""

                            return (FieldSelection (Just src0) l (Just src1))

                    let result =
                                fmap field               fieldSelection
                            <|> fmap projectBySet        labels
                            <|> fmap projectByExpression recordType

                    result

            b <- Text.Megaparsec.many (try (whitespace *> _dot *> alternatives))

            return (foldl' (\e k -> k e) a b) )

    primitiveExpression =
            noted
                ( choice
                    [ temporalLiteral
                    , alternative00
                    , alternative01
                    , alternative02
                    , textLiteral
                    , alternative04
                    , unionType
                    , listLiteral
                    , alternative37
                    , alternative09
                    , builtin
                    ]
                )
            <|> alternative38
          where
            alternative00 = do
                n <- getOffset
                a <- try doubleLiteral
                b <- if isInfinite a
                       then setOffset n *> fail "double out of bounds"
                       else return a
                return (DoubleLit (DhallDouble b))

            alternative01 = do
                a <- try naturalLiteral
                return (NaturalLit a)

            alternative02 = do
                a <- try integerLiteral
                return (IntegerLit a)

            alternative04 = (do
                _openBrace

                src0 <- src whitespace
                mComma <- optional _comma

                -- `src1` corresponds to the prefix whitespace of the first key-value
                -- pair. This is done to avoid using `try` to recover the consumed
                -- whitespace when the comma is not consumed
                src1 <- case mComma of
                    Nothing -> return src0
                    Just _ -> src whitespace

                a <- recordTypeOrLiteral src1

                _closeBrace

                return a ) <?> "literal"

            alternative09 = do
                a <- try doubleInfinity
                return (DoubleLit (DhallDouble a))

            builtin = do
                let predicate c =
                            c == 'N'
                        ||  c == 'I'
                        ||  c == 'D'
                        ||  c == 'L'
                        ||  c == 'O'
                        ||  c == 'B'
                        ||  c == 'S'
                        ||  c == 'T'
                        ||  c == 'F'
                        ||  c == 'K'

                let nan = DhallDouble (0.0/0.0)

                c <- Text.Megaparsec.lookAhead (Text.Megaparsec.satisfy predicate)

                case c of
                    'N' ->
                        choice
                            [ NaturalFold      <$ _NaturalFold
                            , NaturalBuild     <$ _NaturalBuild
                            , NaturalIsZero    <$ _NaturalIsZero
                            , NaturalEven      <$ _NaturalEven
                            , NaturalOdd       <$ _NaturalOdd
                            , NaturalSubtract  <$ _NaturalSubtract
                            , NaturalToInteger <$ _NaturalToInteger
                            , NaturalShow      <$ _NaturalShow
                            , Natural          <$ _Natural
                            , None             <$ _None
                            , DoubleLit nan    <$ _NaN
                            ]
                    'I' ->
                        choice
                            [ IntegerClamp     <$ _IntegerClamp
                            , IntegerNegate    <$ _IntegerNegate
                            , IntegerShow      <$ _IntegerShow
                            , IntegerToDouble  <$ _IntegerToDouble
                            , Integer          <$ _Integer
                            ]

                    'D' ->
                        choice
                            [ Date             <$ _Date
                            , DoubleShow       <$ _DoubleShow
                            , Double           <$ _Double
                            ]
                    'L' ->
                        choice
                            [ ListBuild        <$ _ListBuild
                            , ListFold         <$ _ListFold
                            , ListLength       <$ _ListLength
                            , ListHead         <$ _ListHead
                            , ListLast         <$ _ListLast
                            , ListIndexed      <$ _ListIndexed
                            , ListReverse      <$ _ListReverse
                            , List             <$ _List
                            ]
                    'O' ->    Optional         <$ _Optional
                    'B' ->    Bool             <$ _Bool
                    'S' ->    Const Sort       <$ _Sort
                    'T' ->
                        choice
                            [ TextReplace      <$ _TextReplace
                            , TextShow         <$ _TextShow
                            , Text             <$ _Text
                            , TimeZone         <$ _TimeZone
                            , Time             <$ _Time
                            , BoolLit True     <$ _True
                            , Const Type       <$ _Type
                            ]
                    'F' ->    BoolLit False    <$ _False
                    'K' ->    Const Kind       <$ _Kind
                    _   ->    empty

            alternative37 = do
                a <- identifier
                return (Var a)

            alternative38 = do
                _openParens
                whitespace
                a <- expression
                whitespace
                _closeParens
                return a

    doubleQuotedChunk =
            choice
                [ interpolation
                , unescapedCharacterFast
                , unescapedCharacterSlow
                , escapedCharacter
                ]
          where
            interpolation = do
                _ <- text "${"
                e <- completeExpression_
                _ <- char '}'
                return (Chunks [(mempty, e)] mempty)

            unescapedCharacterFast = do
                t <- Text.Megaparsec.takeWhile1P Nothing predicate
                return (Chunks [] t)
              where
                predicate c =
                    (   ('\x20' <= c && c <= '\x21'    )
                    ||  ('\x23' <= c && c <= '\x5B'    )
                    ||  ('\x5D' <= c && c <= '\x10FFFF')
                    ) && c /= '$'

            unescapedCharacterSlow = do
                _ <- char '$'
                return (Chunks [] "$")

            escapedCharacter = do
                _ <- char '\\'
                c <- choice
                    [ quotationMark
                    , dollarSign
                    , backSlash
                    , forwardSlash
                    , backSpace
                    , formFeed
                    , lineFeed
                    , carriageReturn
                    , tab
                    , unicode
                    ]
                return (Chunks [] (Data.Text.singleton c))
              where
                quotationMark = char '"'

                dollarSign = char '$'

                backSlash = char '\\'

                forwardSlash = char '/'

                backSpace = do _ <- char 'b'; return '\b'

                formFeed = do _ <- char 'f'; return '\f'

                lineFeed = do _ <- char 'n'; return '\n'

                carriageReturn = do _ <- char 'r'; return '\r'

                tab = do _ <- char 't'; return '\t'

                unicode = do
                    _  <- char 'u';

                    let toNumber = Data.List.foldl' (\x y -> x * 16 + y) 0

                    let fourCharacterEscapeSequence = do
                            ns <- Control.Monad.replicateM 4 hexNumber

                            let number = toNumber ns

                            Control.Monad.guard (validCodepoint number)
                                <|> fail "Invalid Unicode code point"

                            return number

                    let bracedEscapeSequence = do
                            _  <- char '{'
                            ns <- some hexNumber

                            let number = toNumber ns

                            Control.Monad.guard (number <= 0x10FFFD && validCodepoint number)
                                <|> fail "Invalid Unicode code point"

                            _  <- char '}'

                            return number

                    n <- bracedEscapeSequence <|> fourCharacterEscapeSequence

                    return (Char.chr n)

    doubleQuotedLiteral = do
            _      <- char '"'
            chunks <- Text.Megaparsec.many doubleQuotedChunk
            _      <- char '"'
            return (mconcat chunks)

    singleQuoteContinue =
            choice
                [ escapeSingleQuotes
                , interpolation
                , escapeInterpolation
                , endLiteral
                , unescapedCharacterFast
                , unescapedCharacterSlow
                , tab
                , endOfLine_
                ]
          where
                escapeSingleQuotes = do
                    _ <- "'''" :: Parser Text
                    b <- singleQuoteContinue
                    return ("''" <> b)

                interpolation = do
                    _ <- text "${"
                    a <- completeExpression_
                    _ <- char '}'
                    b <- singleQuoteContinue
                    return (Chunks [(mempty, a)] mempty <> b)

                escapeInterpolation = do
                    _ <- text "''${"
                    b <- singleQuoteContinue
                    return ("${" <> b)

                endLiteral = do
                    _ <- text "''"
                    return mempty

                unescapedCharacterFast = do
                    a <- Text.Megaparsec.takeWhile1P Nothing predicate
                    b <- singleQuoteContinue
                    return (Chunks [] a <> b)
                  where
                    predicate c =
                        ('\x20' <= c && c <= '\x10FFFF') && c /= '$' && c /= '\''

                unescapedCharacterSlow = do
                    a <- satisfy predicate
                    b <- singleQuoteContinue
                    return (Chunks [] a <> b)
                  where
                    predicate c = c == '$' || c == '\''

                endOfLine_ = do
                    a <- "\n" <|> "\r\n"
                    b <- singleQuoteContinue
                    return (Chunks [] a <> b)

                tab = do
                    _ <- char '\t' <?> "tab"
                    b <- singleQuoteContinue
                    return ("\t" <> b)

    singleQuoteLiteral = do
            _ <- text "''"

            _ <- endOfLine

            a <- singleQuoteContinue

            return (Dhall.Syntax.toDoubleQuoted a)

    textLiteral = (do
            literal <- doubleQuotedLiteral <|> singleQuoteLiteral
            return (TextLit literal) ) <?> "literal"

    recordTypeOrLiteral firstSrc0 =
            choice
                [ emptyRecordLiteral
                , nonEmptyRecordTypeOrLiteral firstSrc0
                , emptyRecordType
                ]

    emptyRecordLiteral = do
        _equal

        _ <- optional (try (whitespace *> _comma))

        whitespace
        return (RecordLit mempty)

    emptyRecordType = return (Record mempty)

    nonEmptyRecordTypeOrLiteral firstSrc0 = do
            let nonEmptyRecordType = do
                    (firstKeySrc1, a) <- try $ do
                        a <- anyLabelOrSome
                        s <- src whitespace
                        _colon
                        return (s, a)

                    firstKeySrc2 <- src nonemptyWhitespace

                    b <- expression

                    e <- Text.Megaparsec.many $ do
                        (src0', c) <- try $ do
                            _comma
                            src0' <- src whitespace
                            c <- anyLabelOrSome
                            return (src0', c)

                        src1 <- src whitespace

                        _colon

                        src2 <- src nonemptyWhitespace

                        d <- expression

                        whitespace

                        return (c, RecordField (Just src0') d (Just src1) (Just src2))

                    _ <- optional (whitespace *> _comma)
                    whitespace

                    m <- toMap ((a, RecordField (Just firstSrc0) b (Just firstKeySrc1) (Just firstKeySrc2)) : e)

                    return (Record m)

            let keysValue maybeSrc = do
                    firstSrc0' <- case maybeSrc of
                        Just src0 -> return src0
                        Nothing -> src whitespace
                    firstLabel <- anyLabelOrSome
                    firstSrc1 <- src whitespace

                    let parseLabelWithWhsp = try $ do
                            _dot
                            src0 <- src whitespace
                            l <- anyLabelOrSome
                            src1 <- src whitespace
                            return (src0, l, src1)

                    restKeys <- Combinators.many parseLabelWithWhsp
                    let keys = (firstSrc0', firstLabel, firstSrc1) :| restKeys

                    let normalRecordEntry = do
                            try _equal

                            lastSrc2 <- src whitespace

                            value <- expression

                            let cons (s0, key, s1) (key', values) =
                                    (key, RecordField (Just s0) (RecordLit [ (key', values) ]) (Just s1) Nothing)

                            let (lastSrc0, lastLabel, lastSrc1) = NonEmpty.last keys
                            let nil = (lastLabel, RecordField (Just lastSrc0) value (Just lastSrc1) (Just lastSrc2))

                            return (foldr cons nil (NonEmpty.init keys))

                    let punnedEntry =
                            case keys of
                                (s0, x, s1) :| [] -> return (x, RecordField (Just s0) (Var (V x 0)) (Just s1) Nothing)
                                _       -> empty

                    (normalRecordEntry <|> punnedEntry) <* whitespace

            let nonEmptyRecordLiteral = do
                    a <- keysValue (Just firstSrc0)

                    as <- many (try (_comma *> keysValue Nothing))

                    _ <- optional (whitespace *> _comma)

                    whitespace

                    let combine k = liftA2 $ \rf rf' -> makeRecordField $ Combine mempty (Just k)
                                                            (recordFieldValue rf')
                                                            (recordFieldValue rf)

                    m <- toMapWith combine (a : as)

                    return (RecordLit m)

            nonEmptyRecordType <|> nonEmptyRecordLiteral

    unionType = (do
            _openAngle

            whitespace

            let unionTypeEntry = do
                    a <- anyLabelOrSome

                    whitespace

                    b <- optional (_colon *> nonemptyWhitespace *> expression <* whitespace)

                    return (a, b)

            let nonEmptyUnionType = do
                    kv <- try (optional (_bar *> whitespace) *> unionTypeEntry)

                    kvs <- many (try (_bar *> whitespace *> unionTypeEntry))

                    m <- toMap (kv : kvs)

                    _ <- optional (_bar *> whitespace)

                    _closeAngle

                    return (Union m)

            let emptyUnionType = do
                    try (optional (_bar *> whitespace) *> _closeAngle)

                    _ <- optional (_bar *> whitespace)

                    return (Union mempty)

            nonEmptyUnionType <|> emptyUnionType ) <?> "literal"

    listLiteral = (do
            _openBracket

            whitespace

            let nonEmptyListLiteral = do
                    a <- try (optional (_comma *> whitespace) *> expression)

                    whitespace

                    as <- many (try (_comma *> whitespace *> expression) <* whitespace)

                    _ <- optional (_comma *> whitespace)

                    _closeBracket

                    return (ListLit Nothing (Data.Sequence.fromList (a : as)))

            let emptyListLiteral = do
                    try (optional (_comma *> whitespace) *> _closeBracket)

                    return (ListLit Nothing mempty)

            nonEmptyListLiteral <|> emptyListLiteral) <?> "literal"

{-| Parse an environment variable import

    This corresponds to the @env@ rule from the official grammar
-}
env :: Parser ImportType
env = do
    _ <- text "env:"
    a <- (alternative0 <|> alternative1)
    return (Env a)
  where
    alternative0 = bashEnvironmentVariable

    alternative1 = do
        _ <- char '"'
        a <- posixEnvironmentVariable
        _ <- char '"'
        return a

-- | Parse a local import without trailing whitespace
localOnly :: Parser ImportType
localOnly =
    choice
        [ parentPath
        , herePath
        , homePath
        , try absolutePath
        ]
  where
    parentPath = do
        _    <- ".." :: Parser Text
        file <- file_ FileComponent

        return (Local Parent file)

    herePath = do
        _    <- "." :: Parser Text
        file <- file_ FileComponent

        return (Local Here file)

    homePath = do
        _    <- "~" :: Parser Text
        file <- file_ FileComponent

        return (Local Home file)

    absolutePath = do
        file <- file_ FileComponent

        return (Local Absolute file)

{-| Parse a local import

    This corresponds to the @local@ rule from the official grammar
-}
local :: Parser ImportType
local = do
    a <- localOnly
    return a

{-| Parse an HTTP(S) import

    This corresponds to the @http@ rule from the official grammar
-}
http :: Parser ImportType
http = do
    url <- httpRaw
    headers <- optional (do
        try (whitespace *> _using *> nonemptyWhitespace)
        importExpression import_ )
    return (Remote (url { headers }))

{-| Parse a `Missing` import

    This corresponds to the @missing@ rule from the official grammar
-}
missing :: Parser ImportType
missing = do
  _missing
  return Missing

{-| Parse an `ImportType`

    This corresponds to the @import-type@ rule from the official grammar
-}
importType_ :: Parser ImportType
importType_ = do
    let predicate c =
            c == '~' || c == '.' || c == '/' || c == 'h' || c == 'e' || c == 'm'

    _ <- Text.Megaparsec.lookAhead (Text.Megaparsec.satisfy predicate)

    choice [ local, http, env, missing ]

{-| Parse a `Dhall.Crypto.SHA256Digest`

    This corresponds to the @hash@ rule from the official grammar
-}
importHash_ :: Parser Dhall.Crypto.SHA256Digest
importHash_ = do
    _ <- text "sha256:"
    t <- count 64 (satisfy hexdig <?> "hex digit")
    let strictBytes16 = Data.Text.Encoding.encodeUtf8 t
    strictBytes <- case Data.ByteArray.Encoding.convertFromBase Base16 strictBytes16 of
        Left  string      -> fail string
        Right strictBytes -> return (strictBytes :: Data.ByteString.ByteString)
    case Dhall.Crypto.sha256DigestFromByteString strictBytes of
      Nothing -> fail "Invalid sha256 hash"
      Just h  -> pure h

{-| Parse an `ImportHashed`

    This corresponds to the @import-hashed@ rule from the official grammar
-}
importHashed_ :: Parser ImportHashed
importHashed_ = do
    importType <- importType_
    hash       <- optional (try (nonemptyWhitespace *> importHash_))
    return (ImportHashed {..})

{-| Parse an `Import`

    This corresponds to the @import@ rule from the official grammar
-}
import_ :: Parser Import
import_ = (do
    importHashed <- importHashed_
    importMode   <- alternative <|> pure Code
    return (Import {..}) ) <?> "import"
  where
    alternative = do
      try (whitespace *> _as *> nonemptyWhitespace)

      (_Text >> pure RawText) <|> (_Location >> pure Location)

-- | 'ApplicationExprInfo' distinguishes certain subtypes of application
-- expressions.
data ApplicationExprInfo
    = NakedMergeOrSomeOrToMap
    -- ^ @merge x y@, @Some x@ or @toMap x@, unparenthesized.
    | ImportExpr
    -- ^ An import expression.
    | ApplicationExpr
    -- ^ Any other application expression.
