module Translator    
where
import Expressions

translate :: AlloyExpr -> SMTExpr
translate (AlloyBinary op x y) = SMTBinary op SMTUnary SMTUnary
