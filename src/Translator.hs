module Translator where
import           Alloy
import           Smt
import           Env

translate :: AlloyExpr -> SmtExpr
translate (AlloyBinary op x y) = SMTBinary op SMTUnary SMTUnary
