{-# LANGUAGE RecordWildCards #-}

module Env where

import           SmtOperators
import           Smt

data Env = RootEnv
  {
    sorts :: [Sort],
    declarations :: [SmtDeclaration],
    assertions :: [Assertion]
  }
  | Env
  {
    auxiliaryFormula::Maybe SmtExpr,
    variablesMap :: [(String, SmtDeclaration)],
    parent :: Env
  } deriving (Show, Eq)

addSort :: Sort -> Env -> Env
addSort s env = case env of
  RootEnv {..} -> env { sorts = s : sorts }
  Env {..}     -> env { parent = p } where p = addSort s parent

getDeclaration :: Env -> String -> SmtDeclaration
getDeclaration env x = case env of
  RootEnv {..} -> getByName declarations x
   where
    getByName (v : vs) n = if name v == n then v else getByName vs n
    getByName _        n = error (n ++ " not found")
  Env {..} -> getDeclaration parent x

containsDeclaration :: Env -> String -> Bool
containsDeclaration RootEnv {..} x =
  any (\declaration -> matchName declaration x) declarations
containsDeclaration Env {..} x = containsDeclaration parent x

matchName :: SmtDeclaration -> String -> Bool
matchName SmtVariable {..} x = x == name
matchName (SortDeclaration (UninterpretedSort x _)) y = x == y
matchName _                _ = error ("Unsupported variable name")

addDeclaration :: Env -> SmtDeclaration -> Env
addDeclaration env f = case env of
  RootEnv {..} -> env { declarations = f : declarations }
  Env {..}     -> env { parent = p } where p = addDeclaration parent f

addDeclarations :: Env -> [SmtDeclaration] -> Env
addDeclarations = foldl addDeclaration

addAssertion :: Env -> Assertion -> Env
addAssertion env a = case env of
  RootEnv {..} -> env { assertions = a : assertions }
  Env {..}     -> env { parent = p } where p = addAssertion parent a


addAssertions :: Env -> [Assertion] -> Env
addAssertions = foldl addAssertion



getVariable :: Env -> String -> SmtDeclaration
getVariable env x = case env of
  RootEnv {..} -> getDeclaration env x
  Env {..}     -> get variablesMap x
   where
    get []           _ = getVariable parent x -- lookup the variable in the smt script
    get ((k, v) : t) _ = if k == x then v else (get t x)

contains :: Env -> String -> Bool
contains env x = case env of
  RootEnv {..} -> containsDeclaration env x
  Env {..} ->
    any (\(string, _) -> x == string) variablesMap || (contains parent x)

addVariable :: Env -> SmtDeclaration -> Env
addVariable env variable =
  env { variablesMap = (name variable, variable) : variablesMap env }


addVariables :: Env -> [SmtDeclaration] -> Env
addVariables = foldl addVariable

first :: (a, b) -> a
first (x, _) = x


second :: (a, b) -> b
second (_, y) = y

emptyRootEnv :: Env
emptyRootEnv = RootEnv
  { sorts        = [uninterpretedAtom, uninterpretedUInt]
  , declarations = [univAtom, univInt, none, intValue, idenAtom]
  , assertions   = []
  }

emptyEnv :: Env
emptyEnv =
  Env { auxiliaryFormula = Nothing, variablesMap = [], parent = emptyRootEnv }

addAuxiliaryFormula :: Env -> SmtExpr -> Env
addAuxiliaryFormula (Env f m p) (SmtQt Exists newVars newBody) = case f of
  Nothing -> Env (Just (SmtQt Exists newVars newBody)) m p
  Just (SmtQt Exists oldVars oldBody) -> Env (Just newF) m p
   where
    newF =
      SmtQt Exists (oldVars ++ newVars) (SmtMultiArity And [oldBody, newBody])
  _ -> error "Only an existential expression can be an auxiliary formula"

addAuxiliaryFormula RootEnv {..} _ =
  error "Auxiliary formulas are only for nested environments"
addAuxiliaryFormula _ f = error ("Unexpected formula" ++ (show f))
