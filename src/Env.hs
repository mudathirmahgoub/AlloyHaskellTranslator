{-# LANGUAGE RecordWildCards #-}

module Env where

import           Smt

data Env = Env
  {
    sorts :: [Sort],
    declarations :: [SmtDeclaration],
    assertions :: [Assertion],
    auxiliaryFormula::Maybe SmtExpr,
    variablesMap :: [(String, SmtDeclaration)],
    lastIndex :: Int
  }

addSort :: Sort -> Env -> Env
addSort s env = env { sorts = s : sorts env }

getDeclaration :: Env -> String -> SmtDeclaration
getDeclaration env x = getByName (declarations env) x
 where
  getByName (v : vs) n = if name v == n then v else getByName vs n
  getByName _        n = error (n ++ " not found")

containsDeclaration :: Env -> String -> Bool
containsDeclaration Env {..} x =
  any (\declaration -> matchName declaration x) declarations

matchName :: SmtDeclaration -> String -> Bool
matchName SmtVariable {..} x = x == name
matchName (SortDeclaration (UninterpretedSort x _)) y = x == y
matchName _                _ = error ("Unsupported variable name")

addDeclaration :: Env -> SmtDeclaration -> Env
addDeclaration env f = env { declarations = f : declarations env }

addDeclarations :: Env -> [SmtDeclaration] -> Env
addDeclarations = foldl addDeclaration

addAssertion :: Env -> Assertion -> Env
addAssertion env a = env { assertions = a : assertions env }


addAssertions :: Env -> [Assertion] -> Env
addAssertions = foldl addAssertion



getVariable :: (Env, Env) -> String -> SmtDeclaration
getVariable (env, Env {..}) x = get variablesMap x
 where
  get []           _ = getDeclaration env x -- lookup the variable in the smt script
  get ((k, v) : t) _ = if k == x then v else (get t x)

contains :: (Env, Env) -> String -> Bool
contains (env, Env {..}) x =
  any (\(string, _) -> x == string) variablesMap || (containsDeclaration env x)

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
emptyEnv = Env { sorts            = [uninterpretedAtom, uninterpretedUInt]
               , declarations     = []
               , assertions       = []
               , auxiliaryFormula = Nothing
               , variablesMap     = []
               , lastIndex        = 0
               }
