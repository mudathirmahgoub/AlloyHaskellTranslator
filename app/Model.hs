module Model where
import           AlloyOperators
import           Alloy

a :: Sig
a = aSig
 where
  aSig = PrimSig
    { isAbstract       = True
    , children         = [a0, a1]
    , parent           = Univ
    , primLabel        = "A"
    , primMultiplicity = ONEOF
    , primFacts        = []
    , primFields       = [ Decl
                             { names     = [f1, f2]
                             , expr      = AlloyBinary ARROW
                                                       (Signature aSig)
                                                       (Signature aSig)
                             , disjoint  = True
                             , disjoint2 = True
                             }
                         ]
    }

f1 :: AlloyVariable
f1 = AlloyVariable "A/f1" (Prod [a, a])
f2 :: AlloyVariable
f2 = AlloyVariable "A/f2" (Prod [a, a])

a0 :: Sig
a0 = PrimSig { isAbstract       = False
             , children         = []
             , parent           = a
             , primLabel        = "A0"
             , primMultiplicity = ONEOF
             , primFacts        = []
             , primFields       = []
             }
a1 :: Sig
a1 = PrimSig { isAbstract       = False
             , children         = []
             , parent           = a
             , primLabel        = "A1"
             , primMultiplicity = LONEOF
             , primFacts        = []
             , primFields       = []
             }
a2 :: Sig
a2 = SubsetSig { parents            = [a0, a1]
               , subsetLabel        = "A2"
               , subsetMultiplicity = LONEOF
               , subsetFacts        = []
               , subsetFields       = []
               }
b :: Sig
b = PrimSig { isAbstract       = False
            , children         = [b0, b1, b2]
            , parent           = Univ
            , primLabel        = "B"
            , primMultiplicity = SOMEOF
            , primFacts        = []
             , primFields       = [ Decl
                             { names     = [g1]
                             , expr      = AlloyUnary ONEOF (Signature a)
                             , disjoint  = True
                             , disjoint2 = True
                             }
                         ]
            }

g1 :: AlloyVariable
g1 = AlloyVariable "A/g1" (Prod [a, a])

b0 :: Sig
b0 = PrimSig { isAbstract       = False
             , children         = []
             , parent           = b
             , primLabel        = "B0"
             , primMultiplicity = SETOF
             , primFacts        = []
             , primFields       = []
             }

b1 :: Sig
b1 = PrimSig { isAbstract       = False
             , children         = []
             , parent           = b
             , primLabel        = "B1"
             , primMultiplicity = SOMEOF
             , primFacts        = []
             , primFields       = []
             }
b2 :: Sig
b2 = PrimSig { isAbstract       = False
             , children         = []
             , parent           = b
             , primLabel        = "B2"
             , primMultiplicity = SOMEOF
             , primFacts        = []
             , primFields       = []
             }

fact1 :: Fact
fact1 = Fact "fact1 a1 != a2" (AlloyBinary NOT_EQUALS (Signature a1) (Signature a2))

fact2 :: Fact
fact2 = Fact "fact2 b1 != b2" (AlloyBinary NOT_EQUALS (Signature b1) (Signature b2))

alloyModel :: AlloyModel
alloyModel = AlloyModel
  { signatures = [Univ, SigInt, None, a, a0, a1, a2, b, b0, b1, b2]
  , facts      = [fact1, fact2]
  , commands   = []
  }

