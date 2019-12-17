module Expressions
where

data Op
    = Plus
    | Minus
    | Multiply
    | Divide
    deriving (Show, Eq)

data Language = Alloy | SMT deriving (Show, Eq)

data AlloyExpr
    = AlloyUnary
    | AlloyBinary Op AlloyExpr AlloyExpr    
    deriving (Show, Eq)

data SMTExpr
    = SMTUnary
    | SMTBinary Op SMTExpr SMTExpr
    | SMTQuantified
    deriving (Show, Eq)
