module Model where
import           AlloyOperators
import           Alloy
import           Translator

a = PrimSig { isAbstract       = True
            , children         = [a0, a1]
            , parent           = Univ
            , primLabel        = "A"
            , primMultiplicity = ONEOF
            , primFacts        = []
            , primFields       = []
            }

a0 = PrimSig { isAbstract       = False
             , children         = []
             , parent           = a
             , primLabel        = "A0"
             , primMultiplicity = ONEOF
             , primFacts        = []
             , primFields       = []
             }

a1 = PrimSig { isAbstract       = False
             , children         = []
             , parent           = a
             , primLabel        = "A1"
             , primMultiplicity = LONEOF
             , primFacts        = []
             , primFields       = []
             }

a2 = SubsetSig { parents            = [a0, a1]
               , subsetLabel        = "A2"
               , subsetMultiplicity = LONEOF
               , subsetFacts        = []
               , subsetFields       = []
               }

b = PrimSig { isAbstract       = False
            , children         = [b0, b1, b2]
            , parent           = Univ
            , primLabel        = "B"
            , primMultiplicity = ONEOF
            , primFacts        = []
            , primFields       = []
            }

b0 = PrimSig { isAbstract       = False
             , children         = []
             , parent           = b
             , primLabel        = "B0"
             , primMultiplicity = SETOF
             , primFacts        = []
             , primFields       = []
             }


b1 = PrimSig { isAbstract       = False
             , children         = []
             , parent           = b
             , primLabel        = "B1"
             , primMultiplicity = SOMEOF
             , primFacts        = []
             , primFields       = []
             }

b2 = PrimSig { isAbstract       = False
             , children         = []
             , parent           = b
             , primLabel        = "B2"
             , primMultiplicity = SOMEOF
             , primFacts        = []
             , primFields       = []
             }

alloyModel = AlloyModel { signatures = [Univ, SigInt, None, a, a0, a1, a2, b, b0, b1, b2]
                        , facts      = []
                        , commands   = []
                        }
