module Smt where

import           SmtOperators

data SmtProgram
    = SmtProgram
    {
        sorts :: [Sort],
        constants :: [Variable],
        assertions :: [Assertion]
    } deriving (Show, Eq)

emptyProgram = SmtProgram { sorts = [], constants = [], assertions = [] }

addSort :: Sort -> SmtProgram -> SmtProgram
addSort s p = p { sorts = s : sorts p }

getConstant :: SmtProgram -> String -> Variable
getConstant p x = getByName (constants p) x
  where
    getByName (f : fs) x = if name f == x then f else getByName fs x
    getByName _ x = error (x ++ " not found")

addConstant :: SmtProgram -> Variable -> SmtProgram
addConstant p f = p { constants = f : constants p }

addConstants :: SmtProgram -> [Variable] -> SmtProgram
addConstants = foldl addConstant

addAssertion :: Assertion -> SmtProgram -> SmtProgram
addAssertion a p = p { assertions = a : assertions p }

data Variable
    = Variable
    {
        name :: String,
        sort :: Sort,
        isOriginal :: Bool -- is it original alloy name or auxiliary name?
    } deriving (Show, Eq)

data SmtExpr
    = SmtIntConstant Int
    | Var Variable
    | SmtBoolConstant Bool
    | SmtUnary SmtUnaryOp SmtExpr
    | SmtBinary SmtBinaryOp SmtExpr SmtExpr
    | SmtIte SmtExpr SmtExpr SmtExpr
    | SmtLet Variable SmtExpr
    | SmtQuantified SmtQuantifier [Variable] SmtExpr
    | SortExpr Sort
    | SmtMultiArity SmtMultiArityOp [SmtExpr]
    deriving (Show, Eq)

smtTrue = SmtBoolConstant True
smtFalse = SmtBoolConstant False

data Sort = IntSort | Atom | UInt | Tuple [Sort] | Set Sort deriving (Show, Eq)

data Assertion = Assertion String SmtExpr deriving (Show, Eq)


none =
    Variable { name = "none", sort = Set (Tuple [Atom]), isOriginal = False }

univAtom = Variable { name       = "univAtom"
                    , sort       = Set (Tuple [Atom])
                    , isOriginal = False
                    }

idenAtom = Variable { name       = "idenAtom"
                    , sort       = Set (Tuple [Atom, Atom])
                    , isOriginal = False
                    }

univInt =
    Variable { name = "univInt", sort = Set (Tuple [UInt]), isOriginal = False }
