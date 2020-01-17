module Smt where

import           Operators

data SmtProgram
    = SmtProgram
    {
        sorts :: [Sort],
        functions :: [SmtFunction],
        assertions :: [Assertion]
    } deriving (Show, Eq)

addSort :: Sort -> SmtProgram -> SmtProgram
addSort s p = p { sorts = s : sorts p }

addFunction :: SmtProgram -> SmtFunction -> SmtProgram
addFunction p f = p { functions = f : functions p }

addFunctions :: SmtProgram -> [SmtFunction] -> SmtProgram
addFunctions p fs = foldl addFunction p fs

addAssertion :: Assertion -> SmtProgram -> SmtProgram
addAssertion a p = p { assertions = a : assertions p }

data SmtFunction
    = SmtFunction
    {
        name :: String,
        inputSorts :: [Sort],
        outputSort :: Sort,
        isOriginal :: Bool -- is it original alloy name or auxiliary name?
    } deriving (Show, Eq)

data SmtType = SmtInt | SmtAtom | Prod[SmtType] deriving (Show, Eq)

data SmtExpr
    = SmtIntConstant Int
    | Var Variable
    | SmtBoolConstant Bool
    | SmtUnary UnaryOp SmtExpr
    | SmtBinary BinaryOp SmtExpr SmtExpr
    | SmtIte SmtExpr SmtExpr SmtExpr
    | SmtLet Variable SmtExpr
    | SmtQuantified Quantifier [Variable] SmtExpr
    | SortExpr Sort
    deriving (Show, Eq)

data Sort = IntSort | Atom | UInt | Tuple [Sort] | Set Sort deriving (Show, Eq)

data Variable = Variable String SmtType deriving (Show, Eq)

data Assertion = Assertion String SmtExpr deriving (Show, Eq)


none = SmtFunction { name       = "none"
                   , inputSorts = []
                   , outputSort = Set (Tuple [Atom])
                   , isOriginal = False
                   }

univAtom = SmtFunction { name       = "univAtom"
                       , inputSorts = []
                       , outputSort = Set (Tuple [Atom])
                       , isOriginal = False
                       }

idenAtom = SmtFunction { name       = "idenAtom"
                       , inputSorts = []
                       , outputSort = Set (Tuple [Atom, Atom])
                       , isOriginal = False
                       }

univInt = SmtFunction { name       = "univInt"
                      , inputSorts = []
                      , outputSort = Set (Tuple [UInt])
                      , isOriginal = False
                      }
