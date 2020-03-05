module Optimizer where

import           SmtOperators
import           Smt


optimize :: SmtExpr -> SmtExpr
optimize (SmtVar var) = SmtVar var
optimize (SmtBoolConstant x) = SmtBoolConstant x
optimize (SmtUnary op x) = SmtUnary op (optimize x)
optimize (SmtBinary op x y) = SmtBinary op (optimize x) (optimize y)
optimize (SmtIte x y z) = SmtIte (optimize x) (optimize y) (optimize z)
optimize (SmtLet pairs body) = SmtLet pairs (optimize body)
optimize (SortExpr sort) = SortExpr sort    
optimize (SmtMultiArity op exprs) = SmtMultiArity op exprs
optimize (SmtCall f args) = SmtCall f (map optimize args)