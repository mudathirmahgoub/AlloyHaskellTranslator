module Model where
import           AlloyOperators
import           Alloy

a :: Sig
a = aSig
 where
  aSig = PrimSig
    { isAbstract       = False
    , children         = [a0, a1]
    , parent           = Univ
    , primLabel        = "A"
    , primMultiplicity = SOMEOF
    , primFacts        = [aFact1]
    , primFields       = [ Decl
                             { names     = [f1, f2]
                             , expr      = AlloyBinary ARROW
                                                       (Signature aSig)
                                                       (Signature aSig)
                             , disjoint  = False
                             , disjoint2 = False
                             }
                         ]
    }

aFact1 = AlloyUnary SOME (Signature a)


fact1 :: Fact
fact1 =
  Fact "fact1 a1 != a2" (AlloyBinary NOT_EQUALS (Signature a1) (Signature a2))

fact2 :: Fact
fact2 = Fact
  "#A > 3"
  (AlloyBinary Greater
               (AlloyUnary CARDINALITY (Signature a))
               (AlloyConstant "3" SigInt)
  )

f1 :: AlloyVariable
f1 = AlloyVariable "A/f1" (Prod [a, a])
f2 :: AlloyVariable
f2 = AlloyVariable "A/f2" (Prod [a, a])

a0 :: Sig
a0 = PrimSig { isAbstract       = False
             , children         = []
             , parent           = a
             , primLabel        = "A0"
             , primMultiplicity = SOMEOF
             , primFacts        = []
             , primFields       = []
             }
a1 :: Sig
a1 = PrimSig { isAbstract       = False
             , children         = []
             , parent           = a
             , primLabel        = "A1"
             , primMultiplicity = SOMEOF
             , primFacts        = []
             , primFields       = []
             }
a2 :: Sig
a2 = SubsetSig { parents            = [a0, a1]
               , subsetLabel        = "A2"
               , subsetMultiplicity = SOMEOF
               , subsetFacts        = []
               , subsetFields       = []
               }
b :: Sig
b = PrimSig
  { isAbstract       = False
  , children         = [b0, b1, b2]
  , parent           = Univ
  , primLabel        = "B"
  , primMultiplicity = SOMEOF
  , primFacts        = []
  , primFields       = [ Decl { names     = [g1]
                              , expr      = AlloyUnary SOMEOF (Signature a)
                              , disjoint  = False
                              , disjoint2 = False
                              }
                       , Decl
                         { names     = [g2, g3, g4]
                         , expr      = AlloyBinary ANY_ARROW_SOME
                                                   (Signature a)
                                                   (Signature a)
                         , disjoint  = False
                         , disjoint2 = False
                         }
                       ]
  }

g1 :: AlloyVariable
g1 = AlloyVariable "B/g1" (Prod [a, a])

g2 :: AlloyVariable
g2 = AlloyVariable "B/g2" (Prod [a, a, a])

g3 :: AlloyVariable
g3 = AlloyVariable "B/g3" (Prod [a, a, a])

g4 :: AlloyVariable
g4 = AlloyVariable "B/g4" (Prod [a, a, a])


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

fact4 :: Fact
fact4 = Fact
  "fact4 1 = 1"
  (AlloyBinary EQUALS (AlloyConstant "1" SigInt) (AlloyConstant "1" SigInt))

-- integer signatures
x :: Sig
x = SubsetSig { parents            = [SigInt]
              , subsetLabel        = "X"
              , subsetMultiplicity = ONEOF
              , subsetFacts        = []
              , subsetFields       = []
              }
y :: Sig
y = SubsetSig { parents            = [SigInt]
              , subsetLabel        = "Y"
              , subsetMultiplicity = ONEOF
              , subsetFacts        = []
              , subsetFields       = []
              }
z :: Sig
z = SubsetSig { parents            = [SigInt]
              , subsetLabel        = "Z"
              , subsetMultiplicity = ONEOF
              , subsetFacts        = []
              , subsetFields       = []
              }

zFacts :: [Fact]
zFacts =
  [ Fact
    "#X = 2"
    (AlloyBinary EQUALS
                 (AlloyUnary CARDINALITY (Signature x))
                 (AlloyConstant "2" SigInt)
    )
  , Fact
    "#Y = 2"
    (AlloyBinary EQUALS
                 (AlloyUnary CARDINALITY (Signature y))
                 (AlloyConstant "2" SigInt)
    )
  , Fact
    "Z = X + Y"
    (AlloyBinary EQUALS
                 (Signature z)
                 (AlloyCall integerPlus [Signature x, Signature y])
    )
  , Fact
    "g2 ++ g3 = g4"
    (AlloyBinary EQUALS
                 (AlloyBinary PLUSPLUS (AlloyVar g2) (AlloyVar g3))
                 (AlloyVar g4)
    )
  , Fact "g3 != g4" (AlloyBinary NOT_EQUALS (AlloyVar g3) (AlloyVar g4))
  , Fact "some g2"  (AlloyUnary SOME (AlloyVar g2))
  , Fact "some g3"  (AlloyUnary SOME (AlloyVar g3))
  ]

alloyModel :: AlloyModel
alloyModel = AlloyModel
  { signatures = [Univ, SigInt, None, a, a0, a1, a2, b, b0, b1, b2, x, y, z]
  , facts      = [fact1, fact2, fact4] ++ zFacts
  , commands   = []
  }

