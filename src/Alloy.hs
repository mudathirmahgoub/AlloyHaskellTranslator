{-# LANGUAGE RecordWildCards #-}
module Alloy where

import           AlloyOperators
import           Utils
import           Smt

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

data AlloyVariable = AlloyVariable String AlloyType deriving (Eq)
instance Show AlloyVariable where
    show (AlloyVariable x _) = x

data AlloyExpr
    = Signature Sig
    | Field Decl
    | AlloyConstant String Sig
    | AlloyVar AlloyVariable
    | AlloyUnary AlloyUnaryOp AlloyExpr
    | AlloyBinary AlloyBinaryOp AlloyExpr AlloyExpr
    | AlloyITE AlloyExpr AlloyExpr AlloyExpr
    | AlloyQt AlloyQuantifier [Decl] AlloyExpr
    | AlloyLet AlloyVariable AlloyExpr AlloyExpr
    | AlloyList AlloyListOp [AlloyExpr]
    deriving (Show, Eq)

data Decl = Decl
    {
        names :: [AlloyVariable] ,
        expr:: AlloyExpr, -- implies multiplicity constraints
        disjoint:: Bool,
        disjoint2:: Bool
    }
    deriving (Show, Eq)

declNames :: Decl -> [String]
declNames Decl {..} = getNames names
  where
    getNames []       = []
    getNames (x : xs) = n : (getNames xs) where (AlloyVariable n _) = x

splitDecls :: [Decl] -> [Decl]
splitDecls decls = concat (map splitDecl decls)

splitDecl :: Decl -> [Decl]
splitDecl Decl {..} =
    [ Decl { names     = [x]
           , expr      = expr
           , disjoint  = disjoint
           , disjoint2 = disjoint2
           }
    | x <- names
    ]

data Sig
    = PrimSig
    {
        isAbstract:: Bool,
        children:: [Sig], -- only PrimSigs are returned as children
        parent:: Sig,
        primLabel:: String,
        primMultiplicity:: AlloyUnaryOp,
        primFacts :: [AlloyExpr],
        primFields :: [Decl]
    }
    | SubsetSig
    {
        parents:: [Sig],
        subsetLabel:: String,
        subsetMultiplicity:: AlloyUnaryOp,
        subsetFacts :: [AlloyExpr],
        subsetFields :: [Decl]
    }
    | Univ | SigInt | None | SigString

instance Eq Sig where
    x == y = label x == label y


isPrime :: Sig -> Bool
isPrime SubsetSig{} = False
isPrime _           = True

isTopLevel :: Sig -> Bool
isTopLevel Univ                   = True
isTopLevel PrimSig { parent = x } = x == Univ
isTopLevel _                      = False

label :: Sig -> String
label Univ                          = name univAtom
label SigInt                        = name univInt
label None                          = name none
label SigString                     = undefined
label PrimSig { primLabel = x }     = x
label SubsetSig { subsetLabel = x } = x

multiplicity :: Sig -> AlloyUnaryOp
multiplicity Univ                             = SETOF
multiplicity SigInt                           = SETOF
multiplicity None                             = SETOF
multiplicity SigString                        = SETOF
multiplicity PrimSig { primMultiplicity = x } = x
multiplicity SubsetSig { subsetMultiplicity = x } = x

fields :: Sig -> [Decl]
fields Univ                            = []
fields SigInt                          = []
fields None                            = []
fields SigString                       = []
fields PrimSig { primFields = xs }     = xs
fields SubsetSig { subsetFields = xs } = xs

sigfacts :: Sig -> [AlloyExpr]
sigfacts Univ                          = []
sigfacts SigInt                        = []
sigfacts None                          = []
sigfacts SigString                     = []
sigfacts PrimSig { primFacts = x }     = x
sigfacts SubsetSig { subsetFacts = x } = x

instance Show Sig where
    show = label

-- simple version
data AlloyType = Prod [Sig] | AlloyBool deriving (Show, Eq)

alloyType :: AlloyExpr -> AlloyType
alloyType (Signature Univ                     ) = Prod [Univ]
alloyType (Signature SigInt                   ) = Prod [SigInt]
alloyType (Signature None                     ) = Prod [None]
alloyType (Signature SigString                ) = Prod [SigString]
alloyType (Signature PrimSig {..}             ) = Prod [PrimSig { .. }]
alloyType (Signature SubsetSig { parents = x }) = Prod x
alloyType (Field     Decl {..}                ) = alloyType expr
-- unary
alloyType (AlloyConstant _         sig        ) = Prod [sig]
alloyType (AlloyUnary    SOMEOF    x          ) = alloyType x
alloyType (AlloyUnary    LONEOF    x          ) = alloyType x -- review this vs lone
alloyType (AlloyUnary    ONEOF     x          ) = alloyType x
alloyType (AlloyUnary    SETOF     x          ) = alloyType x
alloyType (AlloyUnary    EXACTLYOF _          ) = undefined -- review this
alloyType (AlloyUnary    NOT       _          ) = AlloyBool
alloyType (AlloyUnary    NO        _          ) = AlloyBool
alloyType (AlloyUnary    SOME      _          ) = AlloyBool
alloyType (AlloyUnary    LONE      _          ) = AlloyBool
alloyType (AlloyUnary    ONE       _          ) = AlloyBool
alloyType (AlloyUnary    TRANSPOSE x          ) = Prod (reverse ys)
    where Prod ys = alloyType x
alloyType (AlloyUnary RCLOSURE    x) = alloyType x
alloyType (AlloyUnary CLOSURE     x) = alloyType x
alloyType (AlloyUnary CARDINALITY _) = Prod [SigInt]
alloyType (AlloyUnary CAST2INT    _) = undefined
alloyType (AlloyUnary CAST2SIGINT _) = undefined
alloyType (AlloyUnary NOOP        x) = alloyType x
-- binary expressions
alloyType (AlloyBinary ARROW x y   ) = Prod (xs ++ ys)
  where
    Prod xs = alloyType x
    Prod ys = alloyType y
alloyType (AlloyBinary ANY_ARROW_SOME   x y) = alloyType (AlloyBinary ARROW x y)
alloyType (AlloyBinary ANY_ARROW_ONE    x y) = alloyType (AlloyBinary ARROW x y)
alloyType (AlloyBinary ANY_ARROW_LONE   x y) = alloyType (AlloyBinary ARROW x y)
alloyType (AlloyBinary SOME_ARROW_ANY   x y) = alloyType (AlloyBinary ARROW x y)
alloyType (AlloyBinary SOME_ARROW_SOME  x y) = alloyType (AlloyBinary ARROW x y)
alloyType (AlloyBinary SOME_ARROW_ONE   x y) = alloyType (AlloyBinary ARROW x y)
alloyType (AlloyBinary SOME_ARROW_LONE  x y) = alloyType (AlloyBinary ARROW x y)
alloyType (AlloyBinary ONE_ARROW_ANY    x y) = alloyType (AlloyBinary ARROW x y)
alloyType (AlloyBinary ONE_ARROW_SOME   x y) = alloyType (AlloyBinary ARROW x y)
alloyType (AlloyBinary ONE_ARROW_ONE    x y) = alloyType (AlloyBinary ARROW x y)
alloyType (AlloyBinary ONE_ARROW_LONE   x y) = alloyType (AlloyBinary ARROW x y)
alloyType (AlloyBinary LONE_ARROW_ANY   x y) = alloyType (AlloyBinary ARROW x y)
alloyType (AlloyBinary LONE_ARROW_SOME  x y) = alloyType (AlloyBinary ARROW x y)
alloyType (AlloyBinary LONE_ARROW_ONE   x y) = alloyType (AlloyBinary ARROW x y)
alloyType (AlloyBinary LONE_ARROW_LONE  x y) = alloyType (AlloyBinary ARROW x y)
alloyType (AlloyBinary ISSEQ_ARROW_LONE _ _) = undefined
alloyType (AlloyBinary JOIN x y) = joinType (alloyType x) (alloyType y)
alloyType (AlloyBinary DOMAIN           _ y) = alloyType y
alloyType (AlloyBinary RANGE            _ y) = alloyType y
alloyType (AlloyBinary INTERSECT        x _) = alloyType x
alloyType (AlloyBinary PLUSPLUS         x _) = alloyType x
alloyType (AlloyBinary PLUS             x _) = alloyType x
alloyType (AlloyBinary IPLUS            _ _) = Prod [SigInt]
alloyType (AlloyBinary MINUS            x _) = alloyType x
alloyType (AlloyBinary IMINUS           _ _) = Prod [SigInt]
alloyType (AlloyBinary MUL              _ _) = Prod [SigInt]
alloyType (AlloyBinary DIV              _ _) = Prod [SigInt]
alloyType (AlloyBinary REM              _ _) = Prod [SigInt]
alloyType (AlloyBinary EQUALS           _ _) = AlloyBool
alloyType (AlloyBinary NOT_EQUALS       _ _) = AlloyBool
alloyType (AlloyBinary IMPLIES          _ _) = AlloyBool
alloyType (AlloyBinary Less             _ _) = AlloyBool
alloyType (AlloyBinary LTE              _ _) = AlloyBool
alloyType (AlloyBinary Greater          _ _) = AlloyBool
alloyType (AlloyBinary GTE              _ _) = AlloyBool
alloyType (AlloyBinary NOT_LT           _ _) = AlloyBool
alloyType (AlloyBinary NOT_LTE          _ _) = AlloyBool
alloyType (AlloyBinary NOT_GT           _ _) = AlloyBool
alloyType (AlloyBinary NOT_GTE          _ _) = AlloyBool
alloyType (AlloyBinary SHL              _ _) = undefined
alloyType (AlloyBinary SHA              _ _) = undefined
alloyType (AlloyBinary SHR              _ _) = undefined
alloyType (AlloyBinary IN               _ _) = AlloyBool
alloyType (AlloyBinary NOT_IN           _ _) = AlloyBool
alloyType (AlloyBinary AND              _ _) = AlloyBool
alloyType (AlloyBinary OR               _ _) = AlloyBool
alloyType (AlloyBinary IFF              _ _) = AlloyBool
-- if then else expression
alloyType (AlloyITE    _                x _) = alloyType x
-- quantified expression
alloyType (AlloyQt     _                _ _) = AlloyBool
-- let expression
alloyType (AlloyLet    _                _ x) = alloyType x


joinType :: AlloyType -> AlloyType -> AlloyType
joinType AlloyBool _         = error "Can not apply join to boolean"
joinType _         AlloyBool = error "Can not apply join to boolean"
joinType (Prod xs) (Prod ys) = Prod ((excludeLast xs) ++ (excludeFirst ys))


isInt :: AlloyExpr -> Bool
isInt x = case alloyType x of
    Prod [SigInt] -> True
    _             -> False


-- erase all multiplicity operators in the given expr
removeMultiplicity :: AlloyExpr -> AlloyExpr
removeMultiplicity (AlloyUnary SOMEOF x) = removeMultiplicity x
removeMultiplicity (AlloyUnary LONEOF x) = removeMultiplicity x
removeMultiplicity (AlloyUnary ONEOF  x) = removeMultiplicity x
removeMultiplicity (AlloyUnary SETOF  x) = removeMultiplicity x
removeMultiplicity (AlloyBinary op x y ) = case op of
    ARROW            -> arrowExpr
    ANY_ARROW_SOME   -> arrowExpr
    ANY_ARROW_ONE    -> arrowExpr
    ANY_ARROW_LONE   -> arrowExpr
    SOME_ARROW_ANY   -> arrowExpr
    SOME_ARROW_SOME  -> arrowExpr
    SOME_ARROW_ONE   -> arrowExpr
    SOME_ARROW_LONE  -> arrowExpr
    ONE_ARROW_ANY    -> arrowExpr
    ONE_ARROW_SOME   -> arrowExpr
    ONE_ARROW_ONE    -> arrowExpr
    ONE_ARROW_LONE   -> arrowExpr
    LONE_ARROW_ANY   -> arrowExpr
    LONE_ARROW_SOME  -> arrowExpr
    LONE_ARROW_ONE   -> arrowExpr
    LONE_ARROW_LONE  -> arrowExpr
    ISSEQ_ARROW_LONE -> arrowExpr
    _                -> AlloyBinary op x y
  where
    arrowExpr = AlloyBinary ARROW (removeMultiplicity x) (removeMultiplicity y)
removeMultiplicity x = x

--                var       -> expr      -> body
--                old       -> new       -> body
--Java Types   :: ExprVar   -> Expr      -> Expr
substitute :: AlloyExpr -> AlloyExpr -> AlloyExpr -> AlloyExpr
substitute (AlloyVar _) _   (AlloyConstant x y) = (AlloyConstant x y)
substitute (AlloyVar x) new (AlloyVar y) = if x == y then new else (AlloyVar y)
substitute (AlloyVar _) _   (Signature x      ) = (Signature x)
substitute (AlloyVar _) _   (Field     x      ) = (Field x)
substitute (AlloyVar x) new (AlloyUnary op y) =
    AlloyUnary op (substitute (AlloyVar x) new y)
substitute (AlloyVar x) new (AlloyBinary op y z) = AlloyBinary
    op
    (substitute (AlloyVar x) new y)
    (substitute (AlloyVar x) new z)
substitute (AlloyVar x) new (AlloyITE a b c) = (AlloyITE u v w)
  where
    u = (substitute (AlloyVar x) new a)
    v = (substitute (AlloyVar x) new b)
    w = (substitute (AlloyVar x) new c)
substitute _ _ x = error ((show x) ++ "not implemented")

--Java types       ExprVar   -> Expr      -> Bool
hasFreeVariable :: AlloyExpr -> AlloyExpr -> Bool
hasFreeVariable (AlloyVar x) (AlloyVar  y      ) = x == y
hasFreeVariable _            (Signature _      ) = False
hasFreeVariable _            (AlloyConstant _ _) = False
hasFreeVariable (AlloyVar x) (AlloyUnary _ y) = hasFreeVariable (AlloyVar x) y
hasFreeVariable (AlloyVar x) (AlloyBinary _ y z) =
    hasFreeVariable (AlloyVar x) y || hasFreeVariable (AlloyVar x) z
hasFreeVariable (AlloyVar x) (AlloyQt _ decls z) =
    notQuantifier && hasFreeVariable (AlloyVar x) z
    where notQuantifier = notElem x (getDeclsVariables decls)

hasFreeVariable (AlloyVar x) (AlloyList _ ys) =
    any (hasFreeVariable (AlloyVar x)) ys
hasFreeVariable (AlloyVar x) (AlloyITE a b c) = u || v || w
  where
    u = (hasFreeVariable (AlloyVar x) a)
    v = (hasFreeVariable (AlloyVar x) b)
    w = (hasFreeVariable (AlloyVar x) c)
hasFreeVariable _ x = error ((show x) ++ "not implemented")

getDeclsVariables :: [Decl] -> [AlloyVariable]
getDeclsVariables decls = concatMap names (splitDecls decls)
