module Env where
import           Expressions
type Env = [(String, AlloyExpr)]

get :: Env -> String -> AlloyExpr
get ((key, value) : tail) x = if key == x then value else get tail x
get _                     x = error (x ++ " not found")
