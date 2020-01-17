{-# LANGUAGE RecordWildCards #-}
module Alloy where

import           AlloyOperators
import           Utils

data AlloyModel
    = AlloyModel
    {
        signatures :: [Sig],
        facts :: [Fact],
        commands :: [Command]
    } deriving (Show, Eq)

data Fact = Fact String AlloyExpr deriving (Show, Eq)

data Command
    = Run AlloyExpr Scope
    | Check AlloyExpr Scope
    deriving (Show, Eq)
data Scope
    = Scope
    {
        sig :: [Sig],
        isExact :: Bool
    }
    deriving (Show, Eq)

data AlloyExpr
    = Signature Sig
    | Field SigField
    | AlloyConstant String Sig
    | AlloyUnary AlloyUnaryOp AlloyExpr
    | AlloyBinary AlloyBinaryOp AlloyExpr AlloyExpr
    | AlloyITE AlloyExpr AlloyExpr AlloyExpr
    | AlloyQt AlloyQuantifier [Decl] AlloyExpr
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
        primMultiplicity:: AlloyUnaryOp,
        primFacts :: [AlloyExpr]
    }
    | SubsetSig
    {
        sigLabel:: String,
        parents:: [Sig],
        subsetLabel:: String,
        subsetMultiplicity:: AlloyUnaryOp,
        subsetFacts :: [AlloyExpr]
    }
    | Univ | SigInt | None | SigString
    deriving (Eq)

isPrime :: Sig -> Bool
isPrime SubsetSig{} = False
isPrime _           = True

isTopLevel :: Sig -> Bool
isTopLevel Univ                     = True
isTopLevel (PrimSig { parent = x }) = (x == Univ)
isTopLevel _                        = False

label :: Sig -> String
label PrimSig { primLabel = x }     = x
label SubsetSig { subsetLabel = x } = x

multiplicity :: Sig -> AlloyUnaryOp
multiplicity PrimSig { primMultiplicity = x }     = x
multiplicity SubsetSig { subsetMultiplicity = x } = x

sigfacts :: Sig -> [AlloyExpr]
sigfacts PrimSig { primFacts = x }     = x
sigfacts SubsetSig { subsetFacts = x } = x

instance Show Sig where
    show x = label x

-- simple version
data AlloyType = Prod [Sig] | AlloyBool deriving (Show, Eq)

typeof :: AlloyExpr -> AlloyType
typeof (Signature Univ                     ) = Prod [Univ]
typeof (Signature SigInt                   ) = Prod [SigInt]
typeof (Signature None                     ) = Prod [None]
typeof (Signature SigString                ) = Prod [SigString]
typeof (Signature PrimSig {..}             ) = Prod [PrimSig { .. }]
typeof (Signature SubsetSig { parents = x }) = Prod x
-- | Field
typeof (AlloyConstant name      sig        ) = Prod [sig]
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
typeof (AlloyUnary    TRANSPOSE x          ) = Prod (reverse ys)
    where Prod ys = typeof x
typeof (AlloyUnary RCLOSURE    x) = typeof x
typeof (AlloyUnary CLOSURE     x) = typeof x
typeof (AlloyUnary CARDINALITY _) = Prod [SigInt]
typeof (AlloyUnary NOOP        x) = typeof x
-- binary expressions
typeof (AlloyBinary ARROW x y   ) = Prod (xs ++ ys)
  where
    Prod xs = typeof x
    Prod ys = typeof y
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
typeof (AlloyBinary IPLUS            _ _) = Prod [SigInt]
typeof (AlloyBinary MINUS            x _) = typeof x
typeof (AlloyBinary IMINUS           _ _) = Prod [SigInt]
typeof (AlloyBinary MUL              _ _) = Prod [SigInt]
typeof (AlloyBinary DIV              _ _) = Prod [SigInt]
typeof (AlloyBinary REM              _ _) = Prod [SigInt]
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
joinType (Prod xs) (Prod ys) =
    Prod ((excludeLast xs) ++ (excludeFirst ys))


isInt :: AlloyExpr -> Bool
isInt x = case typeof x of
    Prod [SigInt] -> True
    _                -> False
