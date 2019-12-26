module Env where

import           Smt

type Env = [(String, SmtExpr)]

get :: Env -> String -> SmtExpr
get ((key, value) : tail) x = if key == x then value else get tail x
get _                     x = error (x ++ " not found")

contains :: Env -> String -> Bool
contains []                    _ = False
contains ((key, value) : tail) x = if key == x then True else contains tail x

put :: Env -> (String, SmtExpr) -> Env
put env entry = entry : env


first :: (a, b) -> a
first (x, _) = x


second :: (a, b) -> b
second (_, y) = y
