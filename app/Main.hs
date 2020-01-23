module Main where
import           AlloyOperators
import           Alloy
import           Smt
import           Translator
import           Model

printTranslation :: IO ()
printTranslation = do
    print (alloyType (AlloyBinary JOIN (Signature a) (Signature b)))
    print (alloyType (Signature a))
    print translation
    print (smtType (Var (getConstant translation "field")))
    where
        translation = translateModel alloyModel

main :: IO ()
main = printTranslation
