{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards   #-}

-- | Parse Dhall tokens. Even though we don't have a tokenizer per-se this
---  module is useful for keeping some small parsing utilities.
module Dhall.Parser.Token (
    endOfLine,
    validCodepoint,
    whitespace,
    lineComment,
    blockComment,
    nonemptyWhitespace,
    bashEnvironmentVariable,
    posixEnvironmentVariable,
    ComponentType(..),
    text,
    char,
    file_,
    label,
    anyLabelOrSome,
    anyLabel,
    labels,
    httpRaw,
    hexdig,
    identifier,
    hexNumber,
    doubleLiteral,
    doubleInfinity,
    naturalLiteral,
    integerLiteral,
    _Optional,
    _if,
    _then,
    _else,
    _let,
    _in,
    _as,
    _using,
    _merge,
    _toMap,
    _hashOf,
    _assert,
    _Some,
    _None,
    _NaturalFold,
    _NaturalBuild,
    _NaturalIsZero,
    _NaturalEven,
    _NaturalOdd,
    _NaturalToInteger,
    _NaturalShow,
    _NaturalSubtract,
    _IntegerClamp,
    _IntegerNegate,
    _IntegerShow,
    _IntegerToDouble,
    _DoubleShow,
    _ListBuild,
    _ListFold,
    _ListLength,
    _ListHead,
    _ListLast,
    _ListIndexed,
    _ListReverse,
    _Bool,
    _Natural,
    _Integer,
    _Double,
    _Text,
    _TextReplace,
    _TextShow,
    _List,
    _True,
    _False,
    _NaN,
    _Type,
    _Kind,
    _Sort,
    _Location,
    _equal,
    _or,
    _plus,
    _textAppend,
    _listAppend,
    _and,
    _times,
    _doubleEqual,
    _notEqual,
    _dot,
    _openBrace,
    _closeBrace,
    _openBracket,
    _closeBracket,
    _openAngle,
    _closeAngle,
    _bar,
    _comma,
    _openParens,
    _closeParens,
    _colon,
    _at,
    _equivalent,
    _missing,
    _importAlt,
    _combine,
    _combineTypes,
    _prefer,
    _lambda,
    _forall,
    _arrow,
    _doubleColon,
    _with,
    ) where

import Dhall.Parser.Combinators

import Control.Applicative     (Alternative (..), optional)
import Data.Bits               ((.&.))
import Data.Functor            (void, ($>))
import Data.Text               (Text)
import Dhall.Syntax
import Text.Parser.Combinators (choice, try, (<?>))

import qualified Control.Monad
import qualified Data.Char                  as Char
import qualified Data.Foldable
import qualified Data.HashSet
import qualified Data.List                  as List
import qualified Data.List.NonEmpty
import qualified Data.Scientific            as Scientific
import qualified Data.Text
import qualified Text.Megaparsec
import qualified Text.Megaparsec.Char.Lexer
import qualified Text.Parser.Char
import qualified Text.Parser.Combinators
import qualified Text.Parser.Token

import Numeric.Natural (Natural)

-- | Match an end-of-line character sequence
endOfLine :: Parser Text
endOfLine =
    (   Text.Parser.Char.text "\n"  
    <|> Text.Parser.Char.text "\r\n"
    ) <?> "newline"

-- | Returns `True` if the given `Int` is a valid Unicode codepoint
validCodepoint :: Int -> Bool
validCodepoint c =
    not (category == Char.Surrogate
      || c .&. 0xFFFE == 0xFFFE
      || c .&. 0xFFFF == 0xFFFF)
  where
    category = Char.generalCategory (Char.chr c)

{-| Parse 0 or more whitespace characters (including comments)

    This corresponds to the @whsp@ rule in the official grammar
-}
whitespace :: Parser ()
whitespace = Text.Parser.Combinators.skipMany whitespaceChunk

{-| Parse 1 or more whitespace characters (including comments)

    This corresponds to the @whsp1@ rule in the official grammar
-}
nonemptyWhitespace :: Parser ()
nonemptyWhitespace = Text.Parser.Combinators.skipSome whitespaceChunk

alpha :: Char -> Bool
alpha c = ('\x41' <= c && c <= '\x5A') || ('\x61' <= c && c <= '\x7A')

digit :: Char -> Bool
digit c = '\x30' <= c && c <= '\x39'

alphaNum :: Char -> Bool
alphaNum c = alpha c || digit c

{-| Parse a hex digit (uppercase or lowercase)

    This corresponds to the @HEXDIG@ rule in the official grammar
-}
hexdig :: Char -> Bool
hexdig c =
        ('0' <= c && c <= '9')
    ||  ('A' <= c && c <= 'F')
    ||  ('a' <= c && c <= 'f')

signPrefix :: Num a => Parser (a -> a)
signPrefix = (do
    let positive = fmap (\_ -> id    ) (char '+')
    let negative = fmap (\_ -> negate) (char '-')
    positive <|> negative ) <?> "sign"

{-| Parse a `Dhall.Syntax.Double` literal

    This corresponds to the @double-literal@ rule from the official grammar
-}
doubleLiteral :: Parser Double
doubleLiteral = (do
    -- We don't use `Text.Parser.Token.double` since that consumes trailing
    -- whitespace and there is no whitespace-free alternative.  See:
    --
    -- https://github.com/dhall-lang/dhall-haskell/pull/1646
    -- https://github.com/dhall-lang/dhall-haskell/pull/1647
    --
    -- We also don't use `Text.Megaparsec.Char.Lexer.float` because that
    -- transitively depends on `Data.Char.toTitle` which is broken on older
    -- versions of GHCJS that we still support.  See:
    --
    -- https://github.com/dhall-lang/dhall-haskell/pull/1681
    -- https://github.com/ghcjs/ghcjs-base/issues/62
    --
    -- Also, hand-writing the parser code for `Double` literals helps to better
    -- ensure that we follow the standard exactly as written.
    sign <- signPrefix <|> pure id

    x <- Text.Parser.Token.decimal

    let alternative0 = do
            y <- fraction

            e <- exponent' <|> pure 1

            return ((fromInteger x + y) * e)

    let alternative1 = do
            expo <- exponent'

            return (fromInteger x * expo)

    n <- alternative0 <|> alternative1

    return (sign (Scientific.toRealFloat n)) ) <?> "literal"
  where
    fraction = do
        _ <- Text.Parser.Char.char '.'

        digits <- some Text.Parser.Char.digit

        let snoc y d =
              y + Scientific.scientific (fromIntegral (Char.digitToInt d)) (Scientific.base10Exponent y - 1)

        return (List.foldl' snoc 0 digits)

    exponent' = do
        _ <- Text.Parser.Char.oneOf "eE"

        sign <- signPrefix <|> pure id

        x <- Text.Parser.Token.decimal

        return (Scientific.scientific 1 (fromInteger (sign x)))

{-| Parse a signed @Infinity@

    This corresponds to the @minus-infinity-literal@ and @plus-infinity-literal@
    rules from the official grammar
-}
doubleInfinity :: Parser Double
doubleInfinity = (do
    let negative = fmap (\_ -> negate) (char '-')
    sign <- negative <|> pure id
    a <- text "Infinity" >> return (1.0/0.0)
    return (sign a) ) <?> "literal"

{-| Parse an `Dhall.Syntax.Integer` literal

    This corresponds to the @integer-literal@ rule from the official grammar
-}
integerLiteral :: Parser Integer
integerLiteral = (do
    sign <- signPrefix
    a    <- naturalLiteral
    return (sign (fromIntegral a)) ) <?> "literal"

{-| Parse a `Dhall.Syntax.Natural` literal

    This corresponds to the @natural-literal@ rule from the official grammar
-}
naturalLiteral :: Parser Natural
naturalLiteral = (do
    a <-    try (char '0' >> char 'x' >> Text.Megaparsec.Char.Lexer.hexadecimal)
        <|> decimal
        <|> (char '0' $> 0)
    return a ) <?> "literal"
  where
    decimal = do
        n <- headDigit
        ns <- many tailDigit
        return (mkNum (n:ns))
      where
        headDigit = decimalDigit nonZeroDigit <?> "non-zero digit"
          where
            nonZeroDigit c = '1' <= c && c <= '9'

        tailDigit = decimalDigit digit <?> "digit"

        decimalDigit predicate = do
            c <- Text.Parser.Char.satisfy predicate
            return (fromIntegral (Char.ord c - Char.ord '0'))

        mkNum = Data.Foldable.foldl' step 0
          where
            step acc x = acc * 10 + x


{-| Parse an identifier (i.e. a variable or built-in)

    Variables can have an optional index to disambiguate shadowed variables

    This corresponds to the @identifier@ rule from the official grammar
-}
identifier :: Parser Var
identifier = do
    x <- label

    let indexed = try $ do
            whitespace
            _at
            whitespace
            n <- naturalLiteral
            return (fromIntegral n)

    n <- indexed <|> pure 0
    return (V x n)

whitespaceChunk :: Parser ()
whitespaceChunk =
    choice
        [ void (Dhall.Parser.Combinators.takeWhile1 predicate)
        , void (Text.Parser.Char.text "\r\n" <?> "newline")
        , void lineComment
        , void blockComment
        ] <?> "whitespace"
  where
    predicate c = c == ' ' || c == '\t' || c == '\n'

-- | Parse a hexademical number and convert to the corresponding `Int`
hexNumber :: Parser Int
hexNumber = choice [ hexDigit, hexUpper, hexLower ]
  where
    hexDigit = do
        c <- Text.Parser.Char.satisfy predicate
        return (Char.ord c - Char.ord '0')
      where
        predicate c = '0' <= c && c <= '9'

    hexUpper = do
        c <- Text.Parser.Char.satisfy predicate
        return (10 + Char.ord c - Char.ord 'A')
      where
        predicate c = 'A' <= c && c <= 'F'

    hexLower = do
        c <- Text.Parser.Char.satisfy predicate
        return (10 + Char.ord c - Char.ord 'a')
      where
        predicate c = 'a' <= c && c <= 'f'

-- | Parse a Dhall's single-line comment, starting from `--` and until the
--   last character of the line /before/ the end-of-line character
lineComment :: Parser Text
lineComment = do
    _ <- text "--"

    let predicate c = ('\x20' <= c && c <= '\x10FFFF') || c == '\t'

    commentText <- Dhall.Parser.Combinators.takeWhile predicate

    _ <- endOfLine

    return ("--" <> commentText)

-- | Parsed text doesn't include opening braces
blockComment :: Parser Text
blockComment = do
    _ <- text "{-"
    c <- blockCommentContinue
    pure ("{-" <> c <> "-}")

blockCommentChunk :: Parser Text
blockCommentChunk =
    choice
        [ blockComment  -- Nested block comment
        , characters
        , character
        , endOfLine
        ]
  where
    characters = (Dhall.Parser.Combinators.takeWhile1 predicate)
      where
        predicate c =
                '\x20' <= c && c <= '\x10FFFF' && c /= '-' && c /= '{'
            ||  c == '\n'
            ||  c == '\t'

    character = (Dhall.Parser.Combinators.satisfy predicate)
      where
        predicate c = '\x20' <= c && c <= '\x10FFFF' || c == '\n' || c == '\t'

blockCommentContinue :: Parser Text
blockCommentContinue = endOfComment <|> continue
  where
    endOfComment = void (text "-}") *> pure ""

    continue = do
        c <- blockCommentChunk
        c' <- blockCommentContinue
        pure (c <> c')

simpleLabel :: Bool -> Parser Text
simpleLabel allowReserved = try $ do
    c    <- Text.Parser.Char.satisfy headCharacter
    rest <- Dhall.Parser.Combinators.takeWhile tailCharacter
    let t = Data.Text.cons c rest
    let isNotAKeyword = not $ t `Data.HashSet.member` reservedKeywords
    let isNotAReservedIdentifier = not $ t `Data.HashSet.member` reservedIdentifiers
    Control.Monad.guard (isNotAKeyword && (allowReserved || isNotAReservedIdentifier))
    return t

headCharacter :: Char -> Bool
headCharacter c = alpha c || c == '_'

tailCharacter :: Char -> Bool
tailCharacter c = alphaNum c || c == '_' || c == '-' || c == '/'

backtickLabel :: Parser Text
backtickLabel = do
    _ <- char '`'
    t <- Dhall.Parser.Combinators.takeWhile predicate
    _ <- char '`'
    return t
  where
    predicate c =
            '\x20' <= c && c <= '\x5F'
        ||  '\x61' <= c && c <= '\x7E'

{-| Parse a braced sequence of comma-separated labels

    For example, this is used to parse the record projection syntax

    This corresponds to the @labels@ rule in the official grammar
-}
labels :: Parser [Text]
labels = do
    _openBrace

    whitespace

    nonEmptyLabels <|> emptyLabels
  where
    emptyLabels = do
        try (optional (_comma *> whitespace) *> _closeBrace)

        pure []

    nonEmptyLabels = do
        x  <- try (optional (_comma *> whitespace) *> anyLabelOrSome)

        whitespace

        xs <- many (try (_comma *> whitespace *> anyLabelOrSome) <* whitespace)

        _ <- optional (_comma *> whitespace)

        _closeBrace

        return (x : xs)

{-| Parse a label (e.g. a variable\/field\/alternative name)

    Rejects labels that match built-in names (e.g. @Natural/even@)

    This corresponds to the @nonreserved-label@ rule in the official grammar
-}
label :: Parser Text
label = backtickLabel <|> simpleLabel False <?> "label"

{-| Same as `label` except that built-in names are allowed

    This corresponds to the @any-label@ rule in the official grammar
-}
anyLabel :: Parser Text
anyLabel = (do
    t <- backtickLabel <|> simpleLabel True
    return t ) <?> "any label"

{-| Same as `anyLabel` except that `Some` is allowed

    This corresponds to the @any-label-or-some@ rule in the official grammar
-}

anyLabelOrSome :: Parser Text
anyLabelOrSome = try anyLabel <|> ("Some" <$ _Some)

{-| Parse a valid Bash environment variable name

    This corresponds to the @bash-environment-variable@ rule in the official
    grammar
-}
bashEnvironmentVariable :: Parser Text
bashEnvironmentVariable = satisfy predicate0 <> star (satisfy predicate1)
  where
    predicate0 c = alpha c || c == '_'

    predicate1 c = alphaNum c || c == '_'

{-| Parse a valid POSIX environment variable name, which permits a wider range
    of characters than a Bash environment variable name

    This corresponds to the @posix-environment-variable@ rule in the official
    grammar
-}
posixEnvironmentVariable :: Parser Text
posixEnvironmentVariable = plus posixEnvironmentVariableCharacter

posixEnvironmentVariableCharacter :: Parser Text
posixEnvironmentVariableCharacter =
    escapeCharacter <|> satisfy predicate1
  where
    escapeCharacter = do
        _ <- char '\\'

        c <- Text.Parser.Char.satisfy (`elem` ("\"\\abfnrtv" :: String))

        case c of
            '"'  -> return "\""
            '\\' -> return "\\"
            'a'  -> return "\a"
            'b'  -> return "\b"
            'f'  -> return "\f"
            'n'  -> return "\n"
            'r'  -> return "\r"
            't'  -> return "\t"
            'v'  -> return "\v"
            _    -> empty

    predicate1 c =
            ('\x20' <= c && c <= '\x21')
        ||  ('\x23' <= c && c <= '\x3C')
        ||  ('\x3E' <= c && c <= '\x5B')
        ||  ('\x5D' <= c && c <= '\x7E')

quotedPathCharacter :: Char -> Bool
quotedPathCharacter c =
        ('\x20' <= c && c <= '\x21')
    ||  ('\x23' <= c && c <= '\x2E')
    ||  ('\x30' <= c && c <= '\x10FFFF')

{-| The @pathComponent@ function uses this type to distinguish whether to parse
    a URL path component or a file path component
-}
data ComponentType = URLComponent | FileComponent

-- | Parse a path component
pathComponent :: ComponentType -> Parser Text
pathComponent componentType = do
    _ <- "/" :: Parser Text

    let pathData =
            case componentType of
                FileComponent ->
                    Text.Megaparsec.takeWhile1P Nothing Dhall.Syntax.pathCharacter
                URLComponent ->
                    star pchar

    let quotedPathData = do
            _ <- char '"'
            t <- Text.Megaparsec.takeWhile1P Nothing quotedPathCharacter
            _ <- char '"'
            return t

    case componentType of
        FileComponent -> quotedPathData <|> pathData
        URLComponent -> pathData

-- | Parse a `File`
file_ :: ComponentType -> Parser File
file_ componentType = do
    let emptyPath =
            case componentType of
                URLComponent  -> pure (pure "")
                FileComponent -> empty

    path <- Data.List.NonEmpty.some1 (pathComponent componentType) <|> emptyPath

    let directory = Directory (reverse (Data.List.NonEmpty.init path))
    let file      = Data.List.NonEmpty.last path

    return (File {..})

scheme_ :: Parser Scheme
scheme_ =
        ("http" :: Parser Text)
    *>  ((("s" :: Parser Text) *> pure HTTPS) <|> pure HTTP)
    <*  ("://" :: Parser Text)

{-| Parse an HTTP(S) URL without trailing whitespace

    This corresponds to the @http-raw@ rule in the official grammar
-}
httpRaw :: Parser URL
httpRaw = do
    scheme    <- scheme_
    authority <- authority_
    path      <- file_ URLComponent
    query     <- optional (("?" :: Parser Text) *> query_)

    let headers = Nothing

    return (URL {..})

authority_ :: Parser Text
authority_ = option (try (userinfo <> "@")) <> host <> option (":" <> port)

userinfo :: Parser Text
userinfo = star (satisfy predicate <|> pctEncoded)
  where
    predicate c = unreserved c || subDelims c || c == ':'

host :: Parser Text
host = choice [ ipLiteral, try ipV4Address, domain ]

port :: Parser Text
port = star (satisfy digit)

ipLiteral :: Parser Text
ipLiteral = "[" <> (ipV6Address <|> ipVFuture) <> "]"

ipVFuture :: Parser Text
ipVFuture = "v" <> plus (satisfy hexdig) <> "." <> plus (satisfy predicate)
  where
    predicate c = unreserved c || subDelims c || c == ':'

ipV6Address :: Parser Text
ipV6Address =
    choice
        [ try alternative0
        , try alternative1
        , try alternative2
        , try alternative3
        , try alternative4
        , try alternative5
        , try alternative6
        , try alternative7
        ,     alternative8
        ]
  where
    alternative0 = count 6 (h16 <> ":") <> ls32

    alternative1 = "::" <> count 5 (h16 <> ":") <> ls32

    alternative2 = option h16 <> "::" <> count 4 (h16 <> ":") <> ls32

    alternative3 =
            option (h16 <> range 0 1 (try (":" <> h16)))
        <>  "::"
        <>  count 3 (h16 <> ":")
        <>  ls32

    alternative4 =
            option (h16 <> range 0 2 (try (":" <> h16)))
        <>  "::"
        <>  count 2 (h16 <> ":")
        <>  ls32

    alternative5 =
            option (h16 <> range 0 3 (try (":" <> h16)))
        <>  "::"
        <>  h16
        <>  ":"
        <>  ls32

    alternative6 =
        option (h16 <> range 0 4 (try (":" <> h16))) <> "::" <> ls32

    alternative7 =
        option (h16 <> range 0 5 (try (":" <> h16))) <> "::" <> h16

    alternative8 =
        option (h16 <> range 0 6 (try (":" <> h16))) <> "::"

h16 :: Parser Text
h16 = range 1 3 (satisfy hexdig)

ls32 :: Parser Text
ls32 = try (h16 <> ":" <> h16) <|> ipV4Address

ipV4Address :: Parser Text
ipV4Address = decOctet <> "." <> decOctet <> "." <> decOctet <> "." <> decOctet

decOctet :: Parser Text
decOctet =
    choice
        [ try alternative4
        , try alternative3
        , try alternative2
        , try alternative1
        ,     alternative0
        ]
  where
    alternative0 = satisfy digit

    alternative1 = satisfy predicate <> satisfy digit
      where
        predicate c = '\x31' <= c && c <= '\x39'

    alternative2 = "1" <> count 2 (satisfy digit)

    alternative3 = "2" <> satisfy predicate <> satisfy digit
      where
        predicate c = '\x30' <= c && c <= '\x34'

    alternative4 = "25" <> satisfy predicate
      where
        predicate c = '\x30' <= c && c <= '\x35'

domain :: Parser Text
domain = domainLabel <> star ("." <> domainLabel ) <> option "."

domainLabel :: Parser Text
domainLabel = plus alphaNum_ <> star (plus "-" <> plus alphaNum_)
  where
    alphaNum_ = satisfy alphaNum

pchar :: Parser Text
pchar = satisfy predicate <|> pctEncoded
  where
    predicate c = unreserved c || subDelims c || c == ':' || c == '@'

query_ :: Parser Text
query_ = star (pchar <|> satisfy predicate)
  where
    predicate c = c == '/' || c == '?'

pctEncoded :: Parser Text
pctEncoded = "%" <> count 2 (satisfy hexdig)

subDelims :: Char -> Bool
subDelims c = c `elem` ("!$&'*+;=" :: String)

unreserved :: Char -> Bool
unreserved c =
    alphaNum c || c == '-' || c == '.' || c == '_' || c == '~'

{-| A variation on `Text.Parser.Char.text` that doesn't quote the expected
    in error messages
-}
text :: Data.Text.Text -> Parser Text
text t = Text.Parser.Char.text t <?> Data.Text.unpack t
{-# INLINE text #-}

{-| A variation on `Text.Parser.Char.char` that doesn't quote the expected
    token in error messages
-}
char :: Char -> Parser Char
char c = Text.Parser.Char.char c <?> [ c ]
{-# INLINE char #-}

reserved :: Data.Text.Text -> Parser ()
reserved x = void (text x)

reservedChar :: Char -> Parser ()
reservedChar c = void (char c)

builtin :: Data.Text.Text -> Parser ()
builtin x = reserved x <?> "built-in"
{-# INLINE builtin #-}

operator :: Data.Text.Text -> Parser ()
operator x = reserved x <?> "operator"
{-# INLINE operator #-}

operatorChar :: Char -> Parser ()
operatorChar x = reservedChar x <?> "operator"
{-# INLINE operatorChar #-}

keyword :: Data.Text.Text -> Parser ()
keyword x = try (void (text x)) <?> "keyword"

{-| Parse the @if@ keyword

    This corresponds to the @if@ rule from the official grammar
-}
_if :: Parser ()
_if = keyword "if"

{-| Parse the @then@ keyword

    This corresponds to the @then@ rule from the official grammar
-}
_then :: Parser ()
_then = keyword "then"

{-| Parse the @else@ keyword

    This corresponds to the @else@ rule from the official grammar
-}
_else :: Parser ()
_else = keyword "else"

{-| Parse the @let@ keyword

    This corresponds to the @let@ rule from the official grammar
-}
_let :: Parser ()
_let = keyword "let"

{-| Parse the @in@ keyword

    This corresponds to the @in@ rule from the official grammar
-}
_in :: Parser ()
_in = keyword "in"

{-| Parse the @as@ keyword

    This corresponds to the @as@ rule from the official grammar
-}
_as :: Parser ()
_as = keyword "as"

{-| Parse the @using@ keyword

    This corresponds to the @using@ rule from the official grammar
-}
_using :: Parser ()
_using = keyword "using"

{-| Parse the @merge@ keyword

    This corresponds to the @merge@ rule from the official grammar
-}
_merge :: Parser ()
_merge = keyword "merge"

{-| Parse the @toMap@ keyword

    This corresponds to the @toMap@ rule from the official grammar
-}
_toMap :: Parser ()
_toMap = keyword "toMap"

{-| Parse @hasOf@ keyword
  -
    This DO NOT correspont to the official grammar because it is quick
    and dirty hack.
-}
_hashOf :: Parser ()
_hashOf = keyword "hashOf"

{-| Parse the @assert@ keyword

    This corresponds to the @assert@ rule from the official grammar
-}
_assert :: Parser ()
_assert = keyword "assert"

-- | Parse the @with@ keyword
_with :: Parser ()
_with = keyword "with"

{-| Parse the @Some@ built-in

    This corresponds to the @Some@ rule from the official grammar
-}
_Some :: Parser ()
_Some = keyword "Some"

{-| Parse the @None@ built-in

    This corresponds to the @None@ rule from the official grammar
-}
_None :: Parser ()
_None = builtin "None"

{-| Parse the @Natural/fold@ built-in

    This corresponds to the @Natural-fold@ rule from the official grammar
-}
_NaturalFold :: Parser ()
_NaturalFold = builtin "Natural/fold"

{-| Parse the @Natural/build@ built-in

    This corresponds to the @Natural-build@ rule from the official grammar
-}
_NaturalBuild :: Parser ()
_NaturalBuild = builtin "Natural/build"

{-| Parse the @Natural/isZero@ built-in

    This corresponds to the @Natural-isZero@ rule from the official grammar
-}
_NaturalIsZero :: Parser ()
_NaturalIsZero = builtin "Natural/isZero"

{-| Parse the @Natural/even@ built-in

    This corresponds to the @Natural-even@ rule from the official grammar
-}
_NaturalEven :: Parser ()
_NaturalEven = builtin "Natural/even"

{-| Parse the @Natural/odd@ built-in

    This corresponds to the @Natural-odd@ rule from the official grammar
-}
_NaturalOdd :: Parser ()
_NaturalOdd = builtin "Natural/odd"

{-| Parse the @Natural/toInteger@ built-in

    This corresponds to the @Natural-toInteger@ rule from the official grammar
-}
_NaturalToInteger :: Parser ()
_NaturalToInteger = builtin "Natural/toInteger"

{-| Parse the @Natural/show@ built-in

    This corresponds to the @Natural-show@ rule from the official grammar
-}
_NaturalShow :: Parser ()
_NaturalShow = builtin "Natural/show"

{-| Parse the @Natural/subtract@ built-in

    This corresponds to the @Natural-subtract@ rule from the official grammar
-}
_NaturalSubtract :: Parser ()
_NaturalSubtract = builtin "Natural/subtract"

{-| Parse the @Integer/clamp@ built-in

    This corresponds to the @Integer-clamp@ rule from the official grammar
-}
_IntegerClamp :: Parser ()
_IntegerClamp = builtin "Integer/clamp"

{-| Parse the @Integer/negate@ built-in

    This corresponds to the @Integer-negate@ rule from the official grammar
-}
_IntegerNegate :: Parser ()
_IntegerNegate = builtin "Integer/negate"

{-| Parse the @Integer/show@ built-in

    This corresponds to the @Integer-show@ rule from the official grammar
-}
_IntegerShow :: Parser ()
_IntegerShow = builtin "Integer/show"

{-| Parse the @Integer/toDouble@ built-in

    This corresponds to the @Integer-toDouble@ rule from the official grammar
-}
_IntegerToDouble :: Parser ()
_IntegerToDouble = builtin "Integer/toDouble"

{-| Parse the @Double/show@ built-in

    This corresponds to the @Double-show@ rule from the official grammar
-}
_DoubleShow :: Parser ()
_DoubleShow = builtin "Double/show"

{-| Parse the @List/build@ built-in

    This corresponds to the @List-build@ rule from the official grammar
-}
_ListBuild :: Parser ()
_ListBuild = builtin "List/build"

{-| Parse the @List/fold@ built-in

    This corresponds to the @List-fold@ rule from the official grammar
-}
_ListFold :: Parser ()
_ListFold = builtin "List/fold"

{-| Parse the @List/length@ built-in

    This corresponds to the @List-length@ rule from the official grammar
-}
_ListLength :: Parser ()
_ListLength = builtin "List/length"

{-| Parse the @List/head@ built-in

    This corresponds to the @List-head@ rule from the official grammar
-}
_ListHead :: Parser ()
_ListHead = builtin "List/head"

{-| Parse the @List/last@ built-in

    This corresponds to the @List-last@ rule from the official grammar
-}
_ListLast :: Parser ()
_ListLast = builtin "List/last"

{-| Parse the @List/indexed@ built-in

    This corresponds to the @List-indexed@ rule from the official grammar
-}
_ListIndexed :: Parser ()
_ListIndexed = builtin "List/indexed"

{-| Parse the @List/reverse@ built-in

    This corresponds to the @List-reverse@ rule from the official grammar
-}
_ListReverse :: Parser ()
_ListReverse = builtin "List/reverse"

{-| Parse the @Bool@ built-in

    This corresponds to the @Bool@ rule from the official grammar
-}
_Bool :: Parser ()
_Bool = builtin "Bool"

{-| Parse the @Optional@ built-in

    This corresponds to the @Optional@ rule from the official grammar
-}
_Optional :: Parser ()
_Optional = builtin "Optional"

{-| Parse the @Natural@ built-in

    This corresponds to the @Natural@ rule from the official grammar
-}
_Natural :: Parser ()
_Natural = builtin "Natural"

{-| Parse the @Integer@ built-in

    This corresponds to the @Integer@ rule from the official grammar
-}
_Integer :: Parser ()
_Integer = builtin "Integer"

{-| Parse the @Double@ built-in

    This corresponds to the @Double@ rule from the official grammar
-}
_Double :: Parser ()
_Double = builtin "Double"

{-| Parse the @Text@ built-in

    This corresponds to the @Text@ rule from the official grammar
-}
_Text :: Parser ()
_Text = builtin "Text"

{-| Parse the @Text/replace@ built-in

    This corresponds to the @Text-replace@ rule from the official grammar
-}
_TextReplace :: Parser ()
_TextReplace = builtin "Text/replace"

{-| Parse the @Text/show@ built-in

    This corresponds to the @Text-show@ rule from the official grammar
-}
_TextShow :: Parser ()
_TextShow = builtin "Text/show"

{-| Parse the @List@ built-in

    This corresponds to the @List@ rule from the official grammar
-}
_List :: Parser ()
_List = builtin "List"

{-| Parse the @True@ built-in

    This corresponds to the @True@ rule from the official grammar
-}
_True :: Parser ()
_True = builtin "True"

{-| Parse the @False@ built-in

    This corresponds to the @False@ rule from the official grammar
-}
_False :: Parser ()
_False = builtin "False"

{-| Parse a @NaN@ literal

    This corresponds to the @NaN@ rule from the official grammar
-}
_NaN :: Parser ()
_NaN = builtin "NaN"

{-| Parse the @Type@ built-in

    This corresponds to the @Type@ rule from the official grammar
-}
_Type :: Parser ()
_Type = builtin "Type"

{-| Parse the @Kind@ built-in

    This corresponds to the @Kind@ rule from the official grammar
-}
_Kind :: Parser ()
_Kind = builtin "Kind"

{-| Parse the @Sort@ built-in

    This corresponds to the @Sort@ rule from the official grammar
-}
_Sort :: Parser ()
_Sort = builtin "Sort"

{-| Parse the @Location@ keyword

    This corresponds to the @Location@ rule from the official grammar
-}
_Location :: Parser ()
_Location = builtin "Location"

-- | Parse the @=@ symbol
_equal :: Parser ()
_equal = reservedChar '='

-- | Parse the @||@ symbol
_or :: Parser ()
_or = operator "||"

-- | Parse the @+@ symbol
_plus :: Parser ()
_plus = operatorChar '+'

-- | Parse the @++@ symbol
_textAppend :: Parser ()
_textAppend = operator "++"

-- | Parse the @#@ symbol
_listAppend :: Parser ()
_listAppend = operatorChar '#'

-- | Parse the @&&@ symbol
_and :: Parser ()
_and = operator "&&"

-- | Parse the @*@ symbol
_times :: Parser ()
_times = operatorChar '*'

-- | Parse the @==@ symbol
_doubleEqual :: Parser ()
_doubleEqual = operator "=="

-- | Parse the @!=@ symbol
_notEqual :: Parser ()
_notEqual = operator "!="

-- | Parse the @.@ symbol
_dot :: Parser ()
_dot = operatorChar '.'

-- | Parse the @{@ symbol
_openBrace :: Parser ()
_openBrace = reservedChar '{'

-- | Parse the @}@ symbol
_closeBrace :: Parser ()
_closeBrace = reservedChar '}'

-- | Parse the @[@] symbol
_openBracket :: Parser ()
_openBracket = reservedChar '['

-- | Parse the @]@ symbol
_closeBracket :: Parser ()
_closeBracket = reservedChar ']'

-- | Parse the @<@ symbol
_openAngle :: Parser ()
_openAngle = reservedChar '<'

-- | Parse the @>@ symbol
_closeAngle :: Parser ()
_closeAngle = reservedChar '>'

-- | Parse the @|@ symbol
_bar :: Parser ()
_bar = reservedChar '|'

-- | Parse the @,@ symbol
_comma :: Parser ()
_comma = reservedChar ',' <?> "\',\'"

-- | Parse the @(@ symbol
_openParens :: Parser ()
_openParens = reservedChar '('

-- | Parse the @)@ symbol
_closeParens :: Parser ()
_closeParens = reservedChar ')'

-- | Parse the @:@ symbol
_colon :: Parser ()
_colon = reservedChar ':'

-- | Parse the @\@@ symbol
_at :: Parser ()
_at = reservedChar '@' <?> "\"@\""

-- | Parse the equivalence symbol (@===@ or @≡@)
_equivalent :: Parser CharacterSet
_equivalent =
        (Unicode <$ char '≡' <?> "\"≡\"")
    <|> (ASCII <$ text "===" <?> "===")

-- | Parse the @missing@ keyword
_missing :: Parser ()
_missing =
        keyword "missing"
    *>  Text.Megaparsec.notFollowedBy (Text.Parser.Char.satisfy tailCharacter)

-- | Parse the @?@ symbol
_importAlt :: Parser ()
_importAlt = operatorChar '?'

-- | Parse the record combine operator (@/\\@ or @∧@)
_combine :: Parser CharacterSet
_combine =
        (Unicode <$ char '∧' <?> "\"∧\"")
    <|> (ASCII <$ text "/\\" <?> "/\\")

-- | Parse the record type combine operator (@//\\\\@ or @⩓@)
_combineTypes :: Parser CharacterSet
_combineTypes =
        (Unicode <$ char '⩓' <?> "\"⩓\"")
    <|> (ASCII <$ text "//\\\\" <?> "//\\\\")

-- | Parse the record \"prefer\" operator (@//@ or @⫽@)
_prefer :: Parser CharacterSet
_prefer =
        (Unicode <$ char '⫽' <?> "\"⫽\"")
    <|> (ASCII <$ text "//" <?> "//")

-- | Parse a lambda (@\\@ or @λ@)
_lambda :: Parser CharacterSet
_lambda =
        (Unicode <$ char 'λ' <?> "\"λ\"")
    <|> (ASCII <$ char '\\' <?> "\\")

-- | Parse a forall (@forall@ or @∀@)
_forall :: Parser CharacterSet
_forall =
        (Unicode <$ char '∀' <?> "\"∀\"")
    <|> (ASCII <$ text "forall" <?> "forall")

-- | Parse a right arrow (@->@ or @→@)
_arrow :: Parser CharacterSet
_arrow =
        (Unicode <$ char '→' <?> "\"→\"")
    <|> (ASCII <$ text "->" <?> "->")

-- | Parse a double colon (@::@)
_doubleColon :: Parser ()
_doubleColon = operator "::"
