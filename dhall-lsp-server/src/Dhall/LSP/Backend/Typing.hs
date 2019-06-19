module Dhall.LSP.Backend.Typing (annotateLet, exprAt, srcAt, typeAt) where

import Dhall.Context (Context, insert, empty)
import Dhall.Core (Expr(..), Binding(..), subExpressions, normalize, shift, Var(..))
import Dhall.TypeCheck (typeWithA, X(..), TypeError(..))
import Dhall.Parser (Src(..))

import Data.List.NonEmpty (NonEmpty (..))
import Control.Lens (toListOf)
import Data.Text (Text)
import qualified Data.Text as Text
import Control.Applicative ((<|>))
import Data.Functor.Identity (Identity(..))
import Data.Maybe (listToMaybe)
import Control.Monad (join)

import Dhall.LSP.Util (rightToMaybe)
import Dhall.LSP.Backend.Parsing (getLetInner, getLetAnnot)
import Dhall.LSP.Backend.Diagnostics (Position, positionFromMegaparsec, offsetToPosition)

import qualified Data.Text.Prettyprint.Doc                 as Pretty
import qualified Data.Text.Prettyprint.Doc.Render.Text     as Pretty
import Dhall.Pretty (CharacterSet(..), prettyCharacterSet)

-- | Find the type of the subexpression at the given position. Assumes that the
--   input expression is well-typed.
typeAt :: Position -> Expr Src X -> Maybe (Expr Src X)
typeAt pos expr = rightToMaybe (typeAt' pos empty (splitLets expr))

typeAt' :: Position -> Context (Expr Src X) -> Expr Src X -> Either (TypeError Src X) (Expr Src X)
-- the input only contains singleton lets
typeAt' pos ctx (Let (Binding x _ a :| []) (Note src e)) | pos `inside` src = do
  _A <- typeWithA absurd ctx a
  let ctx' = fmap (shift 1 (V x 0)) (insert x _A ctx)
  typeAt' pos ctx' e

typeAt' pos ctx (Lam x _A (Note src b)) | pos `inside` src = do
  let _A' = Dhall.Core.normalize _A
      ctx' = fmap (shift 1 (V x 0)) (insert x _A' ctx)
  typeAt' pos ctx' b

typeAt' pos ctx (Pi x _A  (Note src _B)) | pos `inside` src = do
  let _A' = Dhall.Core.normalize _A
      ctx' = fmap (shift 1 (V x 0)) (insert x _A' ctx)
  typeAt' pos ctx' _B

-- need to catch Notes since the catch-all would remove two layers at once
typeAt' pos ctx (Note _ expr) = typeAt' pos ctx expr

-- catch-all
typeAt' pos ctx expr = do
  let subExprs = toListOf subExpressions expr
  case [ e | (Note src e) <- subExprs, pos `inside` src ] of
    [] -> typeWithA absurd ctx expr  -- return type of whole subexpression
    (t:_) -> typeAt' pos ctx t  -- continue with leaf-expression


-- | Find the smallest Note-wrapped expression at the given position.
exprAt :: Position -> Expr Src a -> Maybe (Expr Src a)
exprAt pos e@(Note _ expr) = exprAt pos expr <|> Just e
exprAt pos expr =
  let subExprs = toListOf subExpressions expr
  in case [ (src, e) | (Note src e) <- subExprs, pos `inside` src ] of
    [] -> Nothing
    ((src,e) : _) -> exprAt pos e <|> Just (Note src e)


-- | Find the smallest Src annotation containing the given position.
srcAt :: Position -> Expr Src a -> Maybe Src
srcAt pos expr = do Note src _ <- exprAt pos expr
                    return src


-- | Given a well-typed expression and a position find the let binder at that
--   position (if there is one) and return a textual update to the source code
--   that inserts the type annotation (or replaces the existing one).
annotateLet :: Position -> Expr Src X -> Maybe (Src, Text)
annotateLet pos expr = annotateLet' pos empty (splitLets expr)

annotateLet' :: Position -> Context (Expr Src X) -> Expr Src X -> Maybe (Src, Text)
annotateLet' pos ctx (Note src e@(Let (Binding _ _ a :| []) _))
  | not $ any (pos `inside`) [ src' | Note src' _ <- toListOf subExpressions e ]
  = do _A <- rightToMaybe $ typeWithA absurd ctx a
       let srcAnnot = case getLetAnnot src of
                        Just x -> x
                        Nothing -> error "The impossible happened: failed\
                                         \ to re-parse a Let expression."
       return (srcAnnot, ": " <> printExpr _A <> " ")

-- binders
annotateLet' pos ctx (Let (Binding x _ a :| []) e@(Note src _))
  | pos `inside` src = do
    _A <- rightToMaybe $ typeWithA absurd ctx a
    let ctx' = fmap (shift 1 (V x 0)) (insert x _A ctx)
    annotateLet' pos ctx' e
annotateLet' pos ctx (Lam x _A b@(Note src _))
  | pos `inside` src = do
    let _A' = Dhall.Core.normalize _A
        ctx' = fmap (shift 1 (V x 0)) (insert x _A' ctx)
    annotateLet' pos ctx' b
annotateLet' pos ctx (Pi x _A _B@(Note src _))
  | pos `inside` src = do
    let _A' = Dhall.Core.normalize _A
        ctx' = fmap (shift 1 (V x 0)) (insert x _A' ctx)
    annotateLet' pos ctx' _B

-- we need to unfold Notes to make progress
annotateLet' pos ctx (Note _ expr) = do
  annotateLet' pos ctx expr

-- catch-all
annotateLet' pos ctx expr =
  let subExprs = toListOf subExpressions expr
  in join $ annotateLet' pos ctx <$> listToMaybe [ Note src e | (Note src e) <- subExprs, pos `inside` src ]


printExpr :: Pretty.Pretty b => Expr a b -> Text
printExpr expr = Pretty.renderStrict $ Pretty.layoutCompact (Pretty.unAnnotate (prettyCharacterSet Unicode expr))


-- Split all multilets into single lets in an expression
splitLets :: Expr Src a -> Expr Src a
splitLets (Note src (Let (b :| (b' : bs)) e)) =
  splitLets (Note src (Let (b :| []) (Note src' (Let (b' :| bs) e))))
  where src' = case getLetInner src of
                 Just x -> x
                 Nothing -> error "The impossible happened: failed\
                                  \ to re-parse a Let expression."
splitLets expr = runIdentity (subExpressions (Identity . splitLets) expr)


-- Check if range lies completely inside a given subexpression.
-- This version takes trailing whitespace into account
-- (c.f. `sanitiseRange` from Backend.Diangostics).
inside :: Position -> Src -> Bool
inside pos (Src left _right txt) =
  let (x1,y1) = positionFromMegaparsec left
      txt' = Text.stripEnd txt
      (dx2,dy2) = (offsetToPosition txt . Text.length) txt'
      (x2,y2) | dx2 == 0 = (x1, y1 + dy2)
              | otherwise = (x1 + dx2, dy2)
  in (x1,y1) <= pos && pos < (x2,y2)
