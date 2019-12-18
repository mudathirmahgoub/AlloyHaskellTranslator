{-# LANGUAGE DeriveAnyClass #-}

module Expressions where

data Op
    = Plus
    | Minus
    | Multiply
    | Divide
    deriving (Show, Eq)

data Language = Alloy | SMT deriving (Show, Eq)

data AlloyExpr
    = AlloyUnary
    | AlloyBinary Op AlloyExpr AlloyExpr
    deriving (Show, Eq)

data SMTExpr
    = SMTUnary
    | SMTBinary Op SMTExpr SMTExpr
    | SMTQuantified
    deriving (Show, Eq)

-- Decl has field expr to support multiplicity constraints
data Decl = Decl{names :: [String] , expr:: AlloyExpr, disjoint:: Bool, disjoint2:: Bool}

data Field = Field{fieldLabel:: String, decl:: Decl}

data Multiplicity = One| Lone | Some| Set deriving (Show, Eq)


class Sig a where
    label :: a -> String
    multiplicity:: a -> multiplicity
    facts :: a -> [AlloyExpr]

data PrimSig = Prim
    {
        isAbstract:: Bool,
        children:: [PrimSig],     
        parent:: PrimSig     
    }
    | Univ | SigInt | None | SigString 
    deriving (Show, Eq, Sig)

-- instance Sig PrimSig where
--     label a = " String"
--     multiplicity x = Lone
--     facts a = []


data Subset = SubsetSig
    {
        sigLabel:: String,        
        parents:: [PrimSig] -- actually it is defined as [Sig]           
    }
    deriving (Show, Eq, Sig)