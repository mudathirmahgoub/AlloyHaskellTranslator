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
optimize (SmtMultiArity op exprs) = SmtMultiArity op (map optimize exprs)
optimize (SmtCall       f  args ) = SmtCall f (map optimize args)


optimizeTupleVariables
  :: [SmtDeclaration] -> SmtExpr -> ([SmtDeclaration], SmtExpr)
optimizeTupleVariables []       expr = ([], expr)
optimizeTupleVariables (x : xs) expr = (x1 ++ x2, y2)
 where
  (x1, y1) = optimizeTupleVariable x expr
  (x2, y2) = optimizeTupleVariables xs y1

optimizeTupleVariable
  :: SmtDeclaration -> SmtExpr -> ([SmtDeclaration], SmtExpr)
optimizeTupleVariable var expr = case sort var of
  Tuple sorts -> (freshVariables, smtLetExpr)
   where
    sortIndexPairs = zipWith (,) sorts [0 .. ((length sorts) - 1)]
    freshVariables = map generateVariable sortIndexPairs
    generateVariable (s, n) = var { name = (name var) ++ (show n), sort = s }
    smtLetExpr = SmtLet [(var, tupleExpr)] expr
    tupleExpr  = SmtMultiArity MkTuple (map SmtVar freshVariables)
  _ -> ([var], expr)


