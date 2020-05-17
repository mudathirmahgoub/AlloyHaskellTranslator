module Main where
import           AlloyOperators
import           Alloy
import           Smt
import           SmtLibPrinter
import           Translator
import           Model
import           Optimizer
import           System.Environment


func :: Either Int Bool -> String
func (Left x) = "Int"
func (Right x) = "Bool"

x = func (Left 5)

y = func (Right True)


printTranslation :: IO ()
printTranslation = do
    putStr translation2
    writeFile "original.smt2"  translation1
    writeFile "optimized.smt2" translation2
  where
    env1         = translateModel alloyModel
    env2         = optimizeEnv env1
    translation1 = (printSmtLibScript env1)
    translation2 = (printSmtLibScript env2)


main :: IO ()
main = printTranslation
