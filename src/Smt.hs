module Smt where

import Operators

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
    deriving (Show, Eq)

data Variable = Variable String SmtType deriving (Show, Eq)