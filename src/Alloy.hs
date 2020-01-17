{-# LANGUAGE RecordWildCards #-}
module Alloy where

import           Operators
import           Utils

data AlloyModel
    = AlloyModel
    {
        signatures :: [Sig],
        commands :: [Command],
        globalFacts :: [AlloyExpr]
    }

data Command
    = Run AlloyExpr Scope
    | Check AlloyExpr Scope

data Scope
    = Scope
    {
        sig :: [Sig],
        isExact :: Bool
    }

data AlloyExpr
    = Signature Sig
    | Field SigField
    | AlloyConstant String Sig
    | AlloyUnary UnaryOp AlloyExpr
    | AlloyBinary BinaryOp AlloyExpr AlloyExpr
    | AlloyITE AlloyExpr AlloyExpr AlloyExpr
    | AlloyQt Quantifier [Decl] AlloyExpr
    | AlloyLet String AlloyExpr AlloyExpr
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

data Sig
    = PrimSig
    {
        isAbstract:: Bool,
        children:: [Sig],
        parent:: Sig,
        primLabel:: String,
        primMultiplicity:: UnaryOp,
        primFacts :: [AlloyExpr]
    }
    | SubsetSig
    {
        sigLabel:: String,
        parents:: [Sig],
        subsetLabel:: String,
        subsetMultiplicity:: UnaryOp,
        subsetFacts :: [AlloyExpr]
    }
    | Univ | SigInt | None | SigString
    deriving (Eq)

isPrime :: Sig -> Bool
isPrime SubsetSig{} = False
isPrime _           = True

label :: Sig -> String
label PrimSig { primLabel = x }     = x
label SubsetSig { subsetLabel = x } = x

multiplicity :: Sig -> UnaryOp
multiplicity PrimSig { primMultiplicity = x }     = x
multiplicity SubsetSig { subsetMultiplicity = x } = x

facts :: Sig -> [AlloyExpr]
facts PrimSig { primFacts = x }     = x
facts SubsetSig { subsetFacts = x } = x

instance Show Sig where
    show x = label x

-- simple version
data AlloyType = Product [Sig] | AlloyBool deriving (Show, Eq)

typeof :: AlloyExpr -> AlloyType
typeof (Signature PrimSig {..}             ) = Product [PrimSig { .. }]
typeof (Signature SubsetSig { parents = x }) = Product x
-- | Field
typeof (AlloyConstant name      sig        ) = Product [sig]
typeof (AlloyUnary    SOMEOF    x          ) = typeof x
typeof (AlloyUnary    LONEOF    x          ) = typeof x -- review this vs lone
typeof (AlloyUnary    ONEOF     x          ) = typeof x
typeof (AlloyUnary    SETOF     x          ) = typeof x
typeof (AlloyUnary    EXACTLYOF x          ) = undefined -- review this
typeof (AlloyUnary    NOT       _          ) = AlloyBool
typeof (AlloyUnary    NO        _          ) = AlloyBool
typeof (AlloyUnary    SOME      _          ) = AlloyBool
typeof (AlloyUnary    LONE      _          ) = AlloyBool
typeof (AlloyUnary    ONE       _          ) = AlloyBool
typeof (AlloyUnary    TRANSPOSE x          ) = Product (reverse ys)
    where Product ys = typeof x
typeof (AlloyUnary RCLOSURE    x) = typeof x
typeof (AlloyUnary CLOSURE     x) = typeof x
typeof (AlloyUnary CARDINALITY _) = Product [SigInt]
typeof (AlloyUnary NOOP        x) = typeof x
-- binary expressions
typeof (AlloyBinary ARROW x y   ) = Product (xs ++ ys)
  where
    Product xs = typeof x
    Product ys = typeof y
typeof (AlloyBinary ANY_ARROW_SOME   x y) = typeof (AlloyBinary ARROW x y)
typeof (AlloyBinary ANY_ARROW_ONE    x y) = typeof (AlloyBinary ARROW x y)
typeof (AlloyBinary ANY_ARROW_LONE   x y) = typeof (AlloyBinary ARROW x y)
typeof (AlloyBinary SOME_ARROW_ANY   x y) = typeof (AlloyBinary ARROW x y)
typeof (AlloyBinary SOME_ARROW_SOME  x y) = typeof (AlloyBinary ARROW x y)
typeof (AlloyBinary SOME_ARROW_ONE   x y) = typeof (AlloyBinary ARROW x y)
typeof (AlloyBinary SOME_ARROW_LONE  x y) = typeof (AlloyBinary ARROW x y)
typeof (AlloyBinary ONE_ARROW_ANY    x y) = typeof (AlloyBinary ARROW x y)
typeof (AlloyBinary ONE_ARROW_SOME   x y) = typeof (AlloyBinary ARROW x y)
typeof (AlloyBinary ONE_ARROW_ONE    x y) = typeof (AlloyBinary ARROW x y)
typeof (AlloyBinary ONE_ARROW_LONE   x y) = typeof (AlloyBinary ARROW x y)
typeof (AlloyBinary LONE_ARROW_ANY   x y) = typeof (AlloyBinary ARROW x y)
typeof (AlloyBinary LONE_ARROW_SOME  x y) = typeof (AlloyBinary ARROW x y)
typeof (AlloyBinary LONE_ARROW_ONE   x y) = typeof (AlloyBinary ARROW x y)
typeof (AlloyBinary LONE_ARROW_LONE  x y) = typeof (AlloyBinary ARROW x y)
typeof (AlloyBinary ISSEQ_ARROW_LONE x y) = undefined
typeof (AlloyBinary JOIN             x y) = joinType (typeof x) (typeof y)
typeof (AlloyBinary DOMAIN           x y) = typeof y
typeof (AlloyBinary RANGE            x y) = typeof y
typeof (AlloyBinary INTERSECT        x _) = typeof x
typeof (AlloyBinary PLUSPLUS         x _) = typeof x
typeof (AlloyBinary PLUS             x _) = typeof x
typeof (AlloyBinary IPLUS            _ _) = Product [SigInt]
typeof (AlloyBinary MINUS            x _) = typeof x
typeof (AlloyBinary IMINUS           _ _) = Product [SigInt]
typeof (AlloyBinary MUL              _ _) = Product [SigInt]
typeof (AlloyBinary DIV              _ _) = Product [SigInt]
typeof (AlloyBinary REM              _ _) = Product [SigInt]
typeof (AlloyBinary EQUALS           _ _) = AlloyBool
typeof (AlloyBinary NOT_EQUALS       _ _) = AlloyBool
typeof (AlloyBinary IMPLIES          _ _) = AlloyBool
typeof (AlloyBinary Less             _ _) = AlloyBool
typeof (AlloyBinary LTE              _ _) = AlloyBool
typeof (AlloyBinary Greater          _ _) = AlloyBool
typeof (AlloyBinary GTE              _ _) = AlloyBool
typeof (AlloyBinary NOT_LT           _ _) = AlloyBool
typeof (AlloyBinary NOT_LTE          _ _) = AlloyBool
typeof (AlloyBinary NOT_GT           _ _) = AlloyBool
typeof (AlloyBinary NOT_GTE          _ _) = AlloyBool
typeof (AlloyBinary SHL              x y) = undefined
typeof (AlloyBinary SHA              x y) = undefined
typeof (AlloyBinary SHR              x y) = undefined
typeof (AlloyBinary IN               _ _) = AlloyBool
typeof (AlloyBinary NOT_IN           _ _) = AlloyBool
typeof (AlloyBinary AND              _ _) = AlloyBool
typeof (AlloyBinary OR               _ _) = AlloyBool
typeof (AlloyBinary IFF              _ _) = AlloyBool
-- if then else expression
typeof (AlloyITE    _                x _) = typeof x
-- quantified expression
typeof (AlloyQt     _                _ _) = AlloyBool
-- let expression
typeof (AlloyLet    _                _ x) = typeof x


joinType :: AlloyType -> AlloyType -> AlloyType
joinType AlloyBool _         = error "Can not apply join to boolean"
joinType _         AlloyBool = error "Can not apply join to boolean"
joinType (Product xs) (Product ys) =
    Product ((excludeLast xs) ++ (excludeFirst ys))
