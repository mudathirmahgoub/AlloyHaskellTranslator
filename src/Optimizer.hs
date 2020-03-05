{-# LANGUAGE RecordWildCards #-}
module Optimizer where

import           SmtOperators
import           Smt
import           Env


optimizeEnv :: Env -> Env
optimizeEnv (RootEnv sorts declarations assertions) = RootEnv
  sorts
  declarations
  (filter (not . isTrivial) (map optimizeAssertion assertions))
optimizeEnv Env {..} = optimizeEnv parent

isTrivial :: Assertion -> Bool
isTrivial (Assertion _ expr) =
  expr == (SmtBoolConstant True) || expr == (SmtMultiArity And [])

optimizeAssertion :: Assertion -> Assertion
optimizeAssertion (Assertion label expr) = Assertion label (optimize expr)

optimize :: SmtExpr -> SmtExpr
optimize (SmtVar          var       ) = SmtVar var
optimize (SmtIntConstant  x         ) = SmtIntConstant x
optimize (SmtBoolConstant x         ) = SmtBoolConstant x
optimize (SmtUnary op x             ) = SmtUnary op (optimize x)
optimize (SmtBinary op x y          ) = SmtBinary op (optimize x) (optimize y)
optimize (SmtIte x y z) = SmtIte (optimize x) (optimize y) (optimize z)
optimize (SmtLet pairs body         ) = SmtLet pairs (optimize body)
optimize (SmtQt quantifier vars body) = optimization1
 where
  (vars1, body1) = optimizeTupleVariables vars body
  body2          = optimize body1
  optimization1  = SmtQt quantifier vars1 body2

optimize (SortExpr sort         ) = SortExpr sort
optimize (SmtMultiArity op exprs) = SmtMultiArity op exprs
optimize (SmtCall       f  args ) = SmtCall f (map optimize args)


optimizeTupleVariables
  :: [SmtDeclaration] -> SmtExpr -> ([SmtDeclaration], SmtExpr)
optimizeTupleVariables vars expr = (vars, expr)
