module Alloy where

import           Operators

data AlloyExpr
    = Prime PrimSig 
    | Subset
    | Field
    | AlloyUnary UnaryOp AlloyExpr
    | AlloyBinary BinaryOp AlloyExpr AlloyExpr
    deriving (Show, Eq)

-- Decl has field expr to support multiplicity constraints
data Decl = Decl{names :: [String] , expr:: AlloyExpr, disjoint:: Bool, disjoint2:: Bool}

data Field = F{fieldLabel:: String, decl:: Decl}

data Multiplicity = One| Lone | Some| Set deriving (Show, Eq)


class Sig a where
    label :: a -> String
    multiplicity:: a -> Multiplicity
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
        primMultiplicity:: Multiplicity,
        primFacts :: [AlloyExpr]
    }
    | Univ | SigInt | None | SigString
    deriving (Show, Eq)

data SubsetSig = SubsetSig
    {
        sigLabel:: String,
        parents:: [PrimSig], -- actually it is defined as [Sig] in Java     
        subsetLabel:: String,
        subsetMultiplicity:: Multiplicity,
        subsetFacts :: [AlloyExpr]
    }
    deriving (Show, Eq)

instance Sig SubsetSig where
    label        = subsetLabel
    multiplicity = subsetMultiplicity
    facts        = subsetFacts

