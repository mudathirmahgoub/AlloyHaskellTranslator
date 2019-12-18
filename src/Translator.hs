module Translator    
where
import Expressions
import Env

translate :: AlloyExpr -> SMTExpr
translate (AlloyBinary op x y) = SMTBinary op SMTUnary SMTUnary
