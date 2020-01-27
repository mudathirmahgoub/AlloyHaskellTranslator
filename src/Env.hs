{-# LANGUAGE RecordWildCards #-}

module Env where

import           Smt

data Env = Env{auxiliaryFormula::Maybe SmtExpr, variablesMap :: [(String, SmtVariable)]}

get :: (SmtScript, Env) -> String -> SmtVariable
get (smtScript, Env {..}) x = getVariable variablesMap x
 where
  getVariable []           _ = getConstant smtScript x -- lookup the variable in the smt script
  getVariable ((k, v) : t) _ = if k == x then v else (getVariable t x)

contains :: (SmtScript, Env) -> String -> Bool
contains (smtScript, Env {..}) x =
  any (\(string, _) -> x == string) variablesMap
    || (containsConstant smtScript x)

put :: Env -> (String, SmtVariable) -> Env
put env entry = env { variablesMap = entry : variablesMap env }


first :: (a, b) -> a
first (x, _) = x


second :: (a, b) -> b
second (_, y) = y

emptyEnv :: Env
emptyEnv = Env { auxiliaryFormula = Nothing, variablesMap = [] }


