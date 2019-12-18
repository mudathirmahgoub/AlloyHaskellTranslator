module Main where
import           Operators
import           Alloy
import           Translator

a = Prim { isAbstract       = False
         , children         = []
         , parent           = Univ
         , primLabel        = "A"
         , primMultiplicity = One
         , primFacts        = []
         }

b = Prim { isAbstract       = False
         , children         = []
         , parent           = Univ
         , primLabel        = "B"
         , primMultiplicity = One
         , primFacts        = []
         }

printTranslation :: IO ()
printTranslation = print (translate (AlloyBinary PLUS (Prime a) (Prime b)))

main :: IO ()
main = printTranslation
