module Main where
import           AlloyOperators
import           Alloy
import           Smt
import           SmtLibPrinter
import           Translator
import           Model 
import           Optimizer

printTranslation :: IO ()
printTranslation = do
    -- print (alloyType (AlloyBinary JOIN (Signature a) (Signature b)))
    -- print (alloyType (Signature a))
    putStr (printSmtLibScript translation2)
    -- print (smtType (SmtVar (getConstant translation "A/f1")))
    -- print (smtType (SmtVar (getConstant translation "A/f2")))
    where 
        translation1 = translateModel alloyModel
        translation2 = optimizeEnv translation1


main :: IO ()
main = printTranslation
