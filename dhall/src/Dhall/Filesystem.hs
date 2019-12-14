{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards   #-}

module Dhall.Filesystem
    ( -- * Filesystem
      filesystem
    , FilesystemError(..)
    ) where

import Control.Exception (Exception)
import Data.Void (Void)
import Dhall.Syntax (Chunks(..), Expr(..))
import System.FilePath ((</>))

import qualified Control.Exception                       as Exception
import qualified Data.Text.Prettyprint.Doc.Render.String as Pretty
import qualified Dhall.Util                              as Util
import qualified Dhall.Map                               as Map
import qualified Dhall.Pretty
import qualified System.Directory                        as Directory
import qualified Data.Text                               as Text
import qualified Data.Text.IO                            as Text.IO

{-| Attempt to transform a Dhall record into a filesystem where:

    * Records are translated into directories

    * `Text` values or fields are translated into files

    For example, the following Dhall record:

    > { dir = { `hello.txt` = "Hello\n" }, `goodbye.txt`= "Goodbye\n" }

    ... should translate to this directory tree:

    > $ tree result
    > result
    > ├── dir
    > │   └── hello.txt
    > └── goodbye.txt
    >
    > $ cat result/dir/hello.txt
    > Hello
    >
    > $ cat result/goodbye.txt
    > Goodbye

    Use this in conjunction with the Prelude's support for rendering JSON/YAML
    in "pure Dhall" so that you can generate files containing JSON.  For
    example:

    > let JSON =
    >       https://prelude.dhall-lang.org/v12.0.0/JSON/package.dhall sha256:843783d29e60b558c2de431ce1206ce34bdfde375fcf06de8ec5bf77092fdef7
    >
    > in  { `example.json` =
    >         JSON.render (JSON.array [ JSON.number 1.0, JSON.bool True ])
    >     , `example.yaml` =
    >         JSON.renderYAML
    >           (JSON.object (toMap { foo = JSON.string "Hello", bar = JSON.null }))
    >     }

    ... which would generate:

    > $ cat result/example.json
    > [ 1.0, true ]
    >
    > $ cat result/example.yaml
    > ! "bar": null
    > ! "foo": "Hello"

    This utility does not take care of type-checking and normalizing the
    provided expression.  This will raise a `FilesystemError` exception upon
    encountering an expression that is not a `TextLit` or `RecordLit`.
-}
filesystem :: FilePath -> Expr Void Void -> IO ()
filesystem path expression = case expression of
    RecordLit keyValues -> do
        let process key value = do
                Directory.createDirectoryIfMissing False path

                filesystem (path </> Text.unpack key) value

        Map.unorderedTraverseWithKey_ process keyValues

    TextLit (Chunks [] text) -> do
        Text.IO.writeFile path text

    _ -> do
        let unexpectedExpression = expression

        Exception.throwIO FilesystemError{..}

{- | This error indicates that you supplied an invalid Dhall expression to the
     `filesystem` function.  The Dhall expression could not be translated to
     a filesystem path.
-}
newtype FilesystemError =
    FilesystemError { unexpectedExpression :: Expr Void Void }

instance Show FilesystemError where
    show FilesystemError{..} =
        Pretty.renderString (Dhall.Pretty.layout message)
      where
        message =
          Util._ERROR <> ": Not a valid filesystem expression\n\
          \                                                                                \n\
          \Explanation: Only a subset of Dhall expressions can be converted to a set of    \n\
          \paths.  Specifically, record literals can be converted to directories and ❰Text❱\n\
          \literals can be converted to files.  No other type of value can be translated to\n\
          \filesystem paths.                                                               \n\
          \                                                                                \n\
          \For example, this is a valid expression that can be translated to filesystem    \n\
          \paths:                                                                          \n\
          \                                                                                \n\
          \                                                                                \n\
          \    ┌──────────────────────────────────┐                                        \n\
          \    │ { `example.json` = \"[1, true]\" } │                                        \n\
          \    └──────────────────────────────────┘                                        \n\
          \                                                                                \n\
          \                                                                                \n\
          \In contrast, the following expression is not allowed due to containing a        \n\
          \❰Natural❱ field, which cannot be translated in this way:                        \n\
          \                                                                                \n\
          \                                                                                \n\
          \    ┌───────────────────────┐                                                   \n\
          \    │ { `example.txt` = 1 } │                                                   \n\
          \    └───────────────────────┘                                                   \n\
          \                                                                                \n\
          \                                                                                \n\
          \You tried to translate the following expression to a filesystem path:           \n\
          \                                                                                \n\
          \" <> Util.insert unexpectedExpression <> "\n\
          \                                                                                \n\
          \... which is neither a ❰Text❱ literal nor a record literal.                     \n"

instance Exception FilesystemError
