{-# LANGUAGE RecordWildCards #-}
module Optimizer where

import           SmtOperators
import           Smt
import           Env


optimizeEnv :: Env -> Env
optimizeEnv (RootEnv sorts declarations assertions) = RootEnv
  sorts
  declarations
  (filter (not . isTrivialAssertion) (map optimizeAssertion assertions))
optimizeEnv Env {..} = optimizeEnv parent

isTrivialAssertion :: Assertion -> Bool
isTrivialAssertion (Assertion _ expr) = isTrivial expr

isTrivial :: SmtExpr -> Bool
isTrivial expr =
  expr == (SmtBoolConstant True) || expr == (SmtMultiArity And [])

optimizeAssertion :: Assertion -> Assertion
optimizeAssertion (Assertion label expr) =
  Assertion label (repeatedlyOptimize (optimize expr))

repeatedlyOptimize :: (SmtExpr, Bool) -> SmtExpr
repeatedlyOptimize (x, False) = x
repeatedlyOptimize (x, True ) = repeatedlyOptimize (optimize x)

optimize :: SmtExpr -> (SmtExpr, Bool)
optimize (SmtVar          var) = (SmtVar var, False)
optimize (SmtIntConstant  x  ) = (SmtIntConstant x, False)
optimize (SmtBoolConstant x  ) = (SmtBoolConstant x, False)
optimize (SmtUnary op x      ) = (smtExpr, changed)
 where
  (optimizedX, changed) = (optimize x)
  smtExpr               = SmtUnary op optimizedX
optimize (SmtBinary op x y) = (smtExpr, changed)
 where
  (optimizedX, changedX) = optimize x
  (optimizedY, changedY) = optimize y
  smtExpr                = SmtBinary op optimizedX optimizedY
  changed                = changedX || changedY
optimize (SmtIte x y z) = (smtExpr, changed)
 where
  (optimizedX, changedX) = optimize x
  (optimizedY, changedY) = optimize y
  (optimizedZ, changedZ) = optimize z
  smtExpr                = SmtIte optimizedX optimizedY optimizedZ
  changed                = changedX || changedY || changedZ

optimize (SmtLet pairs body) = (smtExpr, changed)
 where
  (optimizedBody1, changed) = optimize body
  optimizedBody2            = replaceUnaryTuples pairs optimizedBody1
  replaceUnaryTuples [] y = y
  replaceUnaryTuples ((x, SmtMultiArity MkTuple (x0 : [])) : xs) y =
    replaceExpr (SmtBinary TupSel (SmtIntConstant 0) (SmtVar x)) x0 newY
    where newY = replaceUnaryTuples xs y
  replaceUnaryTuples _ y = y
  smtExpr = SmtLet pairs optimizedBody2

optimize (SmtQt quantifier vars body) = (optimization1, changed)
 where
  (vars1, body1  ) = optimizeTupleVariables vars body
  (body2, changed) = optimize body1
  optimization1    = SmtQt quantifier vars1 body2

optimize (SortExpr sort             ) = (SortExpr sort, False)
optimize (SmtMultiArity And (x : [])) = (smtExpr, True)
  where (smtExpr, _) = optimize x
optimize (SmtMultiArity And (x : xs)) = smtExpr
 where
  (optimizedX, changedX) = optimize x
  optimizedXsPairs       = map optimize xs
  optimizedXs            = filter (not . isTrivial) (map fst optimizedXsPairs)
  changedXs              = any snd optimizedXsPairs
  changed                = changedX || changedXs
  smtExpr                = case optimizedXs of
    [] -> (optimizedX, True)
    _  -> case optimizedX of
      SmtBoolConstant True -> (SmtMultiArity And optimizedXs, True)
      SmtMultiArity And [] -> (SmtMultiArity And optimizedXs, True)
      _ -> (SmtMultiArity And (optimizedX : optimizedXs), changed)
optimize (SmtMultiArity Or (x : [])) = (x, True)
optimize (SmtMultiArity op xs      ) = (smtExpr, changedXs)
 where
  optimizedXsPairs = map optimize xs
  optimizedXs      = map fst optimizedXsPairs
  changedXs        = any snd optimizedXsPairs
  smtExpr          = SmtMultiArity op optimizedXs

optimize (SmtCall f xs) = (smtExpr, changedXs)
 where
  optimizedXsPairs = map optimize xs
  optimizedXs      = map fst optimizedXsPairs
  changedXs        = any snd optimizedXsPairs
  smtExpr          = SmtCall f optimizedXs


optimizeTupleVariables
  :: [SmtDeclaration] -> SmtExpr -> ([SmtDeclaration], SmtExpr)
optimizeTupleVariables []       expr = ([], expr)
optimizeTupleVariables (x : xs) expr = (x1 ++ x2, y2)
 where
  (x1, y1) = optimizeTupleVariable x expr
  (x2, y2) = optimizeTupleVariables xs y1

{-
(forall (x (Tuple Atom UInt)) (expr)) is rewritten as
(forall ((x0 Atom) (x1 UInt)) let ((x (mkTuple x0 x1) (expr)))
-}
optimizeTupleVariable
  :: SmtDeclaration -> SmtExpr -> ([SmtDeclaration], SmtExpr)
optimizeTupleVariable var expr = case sort var of
  Tuple sorts -> (freshVariables, smtLetExpr)
   where
    sortIndexPairs = zip sorts [0 .. ((length sorts) - 1)]
    freshVariables = map generateVariable sortIndexPairs
    generateVariable (s, n) = var { name = (name var) ++ (show n), sort = s }
    smtLetExpr = SmtLet [(var, tupleExpr)] expr
    tupleExpr  = SmtMultiArity MkTuple (map SmtVar freshVariables)
  _ -> ([var], expr)


