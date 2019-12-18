module Translator where
import           Alloy
import           Smt
import           Env

translate :: AlloyExpr -> SmtExpr
translate (AlloyBinary op x y) = SmtBinary op (SmtIntConstant 0) (SmtIntConstant 0)
