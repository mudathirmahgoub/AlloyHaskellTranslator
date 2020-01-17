module Smt where

import           Operators

data SmtProgram
    = SmtProgram
    {
        sorts :: [Sort],
        functions :: [SmtFunction],
        assertions :: [Assertion]
    } deriving (Show, Eq)

emptyProgram = SmtProgram {sorts = [], functions = [], assertions = []}

addSort :: Sort -> SmtProgram -> SmtProgram
addSort s p = p { sorts = s : sorts p }

addFunction :: SmtFunction -> SmtProgram -> SmtProgram
addFunction f p = p { functions = f : functions p }

addAssertion :: Assertion -> SmtProgram -> SmtProgram
addAssertion a p = p { assertions = a : assertions p }

data SmtFunction
    = SmtFunction
    {
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

data Sort = Atom | UInt | Tuple Sort | Set Sort deriving (Show, Eq)

data Variable = Variable String SmtType deriving (Show, Eq)

data Assertion = Assertion String SmtExpr deriving (Show, Eq)
