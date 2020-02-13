{-# LANGUAGE RecordWildCards #-}

module Env where

import           Smt

data Env = Env{auxiliaryFormula::Maybe SmtExpr, variablesMap :: [(String, SmtVariable)]}

getVariable :: (SmtScript, Env) -> String -> SmtVariable
getVariable (smtScript, Env {..}) x = get variablesMap x
 where
  get []           _ = getConstant smtScript x -- lookup the variable in the smt script
  get ((k, v) : t) _ = if k == x then v else (get t x)

contains :: (SmtScript, Env) -> String -> Bool
contains (smtScript, Env {..}) x =
  any (\(string, _) -> x == string) variablesMap
    || (containsConstant smtScript x)

addVariable :: Env -> SmtVariable -> Env
addVariable env variable =
  env { variablesMap = (name variable, variable) : variablesMap env }


addVariables :: Env -> [SmtVariable] -> Env
addVariables = foldl addVariable

first :: (a, b) -> a
first (x, _) = x


second :: (a, b) -> b
second (_, y) = y

emptyEnv :: Env
emptyEnv = Env { auxiliaryFormula = Nothing, variablesMap = [] }


