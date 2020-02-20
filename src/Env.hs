{-# LANGUAGE RecordWildCards #-}

module Env where

import           Smt

data Env = Env{auxiliaryFormula::Maybe SmtExpr, variablesMap :: [(String, SmtDeclaration)], lastIndex :: Int}

getVariable :: (SmtScript, Env) -> String -> SmtDeclaration
getVariable (smtScript, Env {..}) x = get variablesMap x
 where
  get []           _ = getDeclaration smtScript x -- lookup the variable in the smt script
  get ((k, v) : t) _ = if k == x then v else (get t x)

contains :: (SmtScript, Env) -> String -> Bool
contains (smtScript, Env {..}) x =
  any (\(string, _) -> x == string) variablesMap
    || (containsDeclaration smtScript x)

addVariable :: Env -> SmtDeclaration -> Env
addVariable env variable =
  env { variablesMap = (name variable, variable) : variablesMap env }


addVariables :: Env -> [SmtDeclaration] -> Env
addVariables = foldl addVariable

first :: (a, b) -> a
first (x, _) = x


second :: (a, b) -> b
second (_, y) = y

emptyEnv :: Env
emptyEnv = Env { auxiliaryFormula = Nothing, variablesMap = [], lastIndex = 0 }


getFreshIndex :: Env -> Env
getFreshIndex (Env x y z) = Env x y (z + 1)
