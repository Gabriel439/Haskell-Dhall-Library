{-# LANGUAGE OverloadedStrings #-}
module Main (main) where

import Criterion.Main (defaultMain)

import qualified Criterion as Criterion
import qualified Data.Sequence as Seq
import qualified Dhall.Core as Core
import qualified Dhall.Import as Import
import qualified Dhall.TypeCheck as TypeCheck

dhallPreludeImport :: Core.Import
dhallPreludeImport = Core.Import
  { Core.importMode = Core.Code
  , Core.importHashed = Core.ImportHashed
    { Core.hash = Nothing
    , Core.importType = Core.Local Core.Here $ Core.File
      { Core.directory = Core.Directory ["deep-nested-large-record", "benchmark"]
      , Core.file = "prelude.dhall"
      }
    }
  }

issue412 :: Core.Expr s TypeCheck.X -> Criterion.Benchmarkable
issue412 prelude = Criterion.whnf TypeCheck.typeOf expr
  where
    expr
      = Core.Let "prelude" Nothing prelude
      $ Core.ListLit Nothing
      $ Seq.replicate 5
      $ Core.Var (Core.V "prelude" 0) `Core.Field` "types" `Core.Field` "Little" `Core.Field` "Foo"

unionPerformance :: Core.Expr s TypeCheck.X -> Criterion.Benchmarkable
unionPerformance prelude = Criterion.whnf TypeCheck.typeOf expr
  where
    expr =
        Core.Let "x" Nothing
            (Core.Let "big" Nothing (prelude `Core.Field` "types" `Core.Field` "Big")
                (Core.Prefer "big" "big")
            )
            "x"

main :: IO ()
main = do
  prelude <- Import.load (Core.Embed dhallPreludeImport)
  defaultMain
    [ Criterion.bench "issue 412" (issue412 prelude)
    , Criterion.bench "union performance" (unionPerformance prelude)
    ]
