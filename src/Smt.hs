module Smt where

import Operators

data SmtExpr
    = SMTUnary
    | SMTBinary BinaryOp SmtExpr SmtExpr
    | SMTQuantified
    deriving (Show, Eq)