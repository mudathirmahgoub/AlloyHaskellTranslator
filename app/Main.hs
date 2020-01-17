module Main where
import           Operators
import           Alloy
import           Translator

a = PrimSig { isAbstract       = False
         , children         = []
         , parent           = Univ
         , primLabel        = "A"
         , primMultiplicity = ONEOF
         , primFacts        = []
         }

b = PrimSig { isAbstract       = False
         , children         = []
         , parent           = Univ
         , primLabel        = "B"
         , primMultiplicity = ONEOF
         , primFacts        = []
         }

printTranslation :: IO ()
printTranslation = print (typeof  (AlloyBinary JOIN (Signature a) (Signature b)))

main :: IO ()
main = printTranslation
