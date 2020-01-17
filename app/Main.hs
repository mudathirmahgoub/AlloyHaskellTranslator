module Main where
import           AlloyOperators
import           Alloy
import           Translator
import           Model

printTranslation :: IO ()
printTranslation = do
    print (typeof (AlloyBinary JOIN (Signature a) (Signature b)))
    print (typeof (Signature a))
    print (translateModel alloyModel)

main :: IO ()
main = printTranslation
