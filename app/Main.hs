module Main where
import           Operators
import           Alloy
import           Translator

a = Prim { isAbstract       = False
         , children         = []
         , parent           = Univ
         , primLabel        = "A"
         , primMultiplicity = ONEOF
         , primFacts        = []
         }

b = Prim { isAbstract       = False
         , children         = []
         , parent           = Univ
         , primLabel        = "B"
         , primMultiplicity = ONEOF
         , primFacts        = []
         }

printTranslation :: IO ()
printTranslation = print (translate (AlloyBinary PLUS (Prime a) (Prime b)))

main :: IO ()
main = printTranslation
