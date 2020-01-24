{-# LANGUAGE RecordWildCards #-}

module Env where

import           Smt

data Env = Env{auxiliaryFormula::SmtExpr, variablesMap :: [(String, SmtExpr)]}

get :: Env -> String -> SmtExpr
get Env {..} x = getVariable variablesMap x
  where
    getVariable [] _ = error (x ++ " not found")
    getVariable ((key, value) : tail) x =
        if key == x then value else (getVariable tail x)

contains :: Env -> String -> Bool
contains Env {..} x = containsVariable variablesMap x
  where
    containsVariable [] _ = False
    containsVariable ((key, value) : tail) x =
        if key == x then True else (containsVariable tail x)

put :: Env -> (String, SmtExpr) -> Env
put env entry = env { variablesMap = entry : variablesMap env }


first :: (a, b) -> a
first (x, _) = x


second :: (a, b) -> b
second (_, y) = y

emptyEnv = Env { auxiliaryFormula = smtTrue, variablesMap = [] }
