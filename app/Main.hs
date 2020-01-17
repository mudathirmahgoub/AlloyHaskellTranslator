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
printTranslation = do
    print (typeof (AlloyBinary JOIN (Signature a) (Signature b)))
    print (typeof (Signature a))

main :: IO ()
main = printTranslation
