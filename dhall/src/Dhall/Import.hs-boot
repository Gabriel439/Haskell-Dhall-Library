module Dhall.Import where
import Dhall.Syntax (Expr)
import Data.Void (Void)
import Dhall.Crypto (SHA256Digest)

hashExpression :: Expr Void Void -> SHA256Digest
