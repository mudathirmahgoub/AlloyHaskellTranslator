module Alloy where

import           Operators

data AlloyExpr
    = Prime PrimSig
    | Subset SubsetSig
    | Field SigField
    | AlloyConstant String PrimSig
    | AlloyUnary UnaryOp AlloyExpr
    | AlloyBinary BinaryOp AlloyExpr AlloyExpr
    | AlloyITE AlloyExpr AlloyExpr AlloyExpr
    | AlloyQt Quantifier AlloyExpr
    deriving (Show, Eq)

-- Decl has field expr to support multiplicity constraints
data Decl = Decl
    {
        names :: [String] ,
        expr:: AlloyExpr,
        disjoint:: Bool,
        disjoint2:: Bool
    }
    deriving (Show, Eq)

data SigField = SigField {fieldLabel:: String, decl:: Decl} deriving (Show, Eq)

class Sig a where
    label :: a -> String
    multiplicity:: a -> UnaryOp
    facts :: a -> [AlloyExpr]



instance Sig PrimSig where
    label        = primLabel
    multiplicity = primMultiplicity
    facts        = primFacts

data PrimSig = Prim
    {
        isAbstract:: Bool,
        children:: [PrimSig],
        parent:: PrimSig,
        primLabel:: String,
        primMultiplicity:: UnaryOp,
        primFacts :: [AlloyExpr]
    }
    | Univ | SigInt | None | SigString
    deriving (Show, Eq)

data SubsetSig = SubsetSig
    {
        sigLabel:: String,
        parents:: [PrimSig], -- actually it is defined as [Sig] in Java     
        subsetLabel:: String,
        subsetMultiplicity:: UnaryOp,
        subsetFacts :: [AlloyExpr]
    }
    deriving (Show, Eq)

instance Sig SubsetSig where
    label        = subsetLabel
    multiplicity = subsetMultiplicity
    facts        = subsetFacts

-- simple version
data AlloyType = Product [PrimSig] | AlloyBool deriving (Show, Eq)

typeof :: AlloyExpr -> AlloyType
typeof (Prime  x                     ) = Product [x]
typeof (Subset x                     ) = Product (parents x)
-- | Field
typeof (AlloyConstant name        sig) = Product [sig]
typeof (AlloyUnary    SOMEOF      x  ) = typeof x
typeof (AlloyUnary    LONEOF      x  ) = typeof x -- review this vs lone
typeof (AlloyUnary    ONEOF       x  ) = typeof x
typeof (AlloyUnary    SETOF       x  ) = typeof x
typeof (AlloyUnary    EXACTLYOF   x  ) = undefined -- review this
typeof (AlloyUnary    NOT         _  ) = AlloyBool
typeof (AlloyUnary    NO          _  ) = AlloyBool
typeof (AlloyUnary    SOME        _  ) = AlloyBool
typeof (AlloyUnary    LONE        _  ) = AlloyBool
typeof (AlloyUnary    ONE         _  ) = AlloyBool
typeof (AlloyUnary    TRANSPOSE   x  ) = Product (reverse y) where Product y = typeof x
typeof (AlloyUnary    RCLOSURE    x  ) = undefined
typeof (AlloyUnary    CLOSURE     x  ) = typeof x
typeof (AlloyUnary    CARDINALITY _  ) = Product [SigInt]
typeof (AlloyUnary    NOOP        x  ) = typeof x

-- | AlloyBinary BinaryOp AlloyExpr AlloyExpr
-- | AlloyITE AlloyExpr AlloyExpr AlloyExpr
-- | AlloyQt Quantifier AlloyExpr

