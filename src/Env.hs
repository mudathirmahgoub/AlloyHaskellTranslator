{-# LANGUAGE RecordWildCards #-}

module Env where

import           Smt

data Env = Env{auxiliaryFormula::Maybe SmtExpr, variablesMap :: [(String, SmtVariable)]}

get :: Env -> String -> SmtVariable
get Env {..} x = getVariable variablesMap x
 where
  getVariable []           _ = error (x ++ " not found")
  getVariable ((k, v) : t) _ = if k == x then v else (getVariable t x)

contains :: Env -> String -> Bool
contains Env {..} = containsVariable variablesMap
 where
  containsVariable []           _ = False
  containsVariable ((k, _) : t) x = k == x || (containsVariable t x)

put :: Env -> (String, SmtVariable) -> Env
put env entry = env { variablesMap = entry : variablesMap env }


first :: (a, b) -> a
first (x, _) = x


second :: (a, b) -> b
second (_, y) = y

emptyEnv :: Env
emptyEnv = Env { auxiliaryFormula = Nothing, variablesMap = [] }


