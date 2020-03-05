{-# LANGUAGE RecordWildCards #-}
module Smt where

import           Utils
import           SmtOperators


-- instance Show (State Int Int) where
--     show = "x"

-- instance Show Stateful where
--     show (Stateful x) = show x

-- instance Eq Stateful where
--     (Stateful x1 y1) == (Stateful x2 y2) = (x1 == x2) && (y1 == y2)

data SmtDeclaration
    = SmtVariable
    {
        name :: String,
        sort :: Sort,
        isOriginal :: Bool, -- is it original smtScript name or auxiliary name?
        arguments :: [Sort] -- zero if the function is constant
    }
    | SortDeclaration Sort
    deriving (Eq)

instance Show SmtDeclaration where
    show SmtVariable { name = x } = x
    show (SortDeclaration x)      = show x

data SmtExpr
    = SmtIntConstant Int
    | SmtVar SmtDeclaration
    | SmtBoolConstant Bool
    | SmtUnary SmtUnaryOp SmtExpr
    | SmtBinary SmtBinaryOp SmtExpr SmtExpr
    | SmtIte SmtExpr SmtExpr SmtExpr
    | SmtLet [(SmtDeclaration, SmtExpr)] SmtExpr
    | SmtQt SmtQuantifier [SmtDeclaration] SmtExpr
    | SortExpr Sort
    | SmtMultiArity SmtMultiArityOp [SmtExpr]
    | SmtCall SmtDeclaration [SmtExpr]
    deriving (Show, Eq)

smtTrue :: SmtExpr
smtTrue = SmtBoolConstant True

smtFalse :: SmtExpr
smtFalse = SmtBoolConstant False

data Sort = SmtInt | SmtBool | Tuple [Sort] | Set Sort | UninterpretedSort String Int deriving (Show, Eq)

uninterpretedAtom :: Sort
uninterpretedAtom = UninterpretedSort "Atom" 0
uninterpretedUInt :: Sort
uninterpretedUInt = UninterpretedSort "UInt" 0

data Assertion = Assertion String SmtExpr deriving (Show, Eq)

none :: SmtDeclaration
none = SmtVariable { name       = "none"
                   , sort       = Set (Tuple [uninterpretedAtom])
                   , isOriginal = False
                   , arguments  = []
                   }

univAtom :: SmtDeclaration
univAtom = SmtVariable { name       = "univAtom"
                       , sort       = Set (Tuple [uninterpretedAtom])
                       , isOriginal = False
                       , arguments  = []
                       }

idenAtom :: SmtDeclaration
idenAtom = SmtVariable
    { name       = "idenAtom"
    , sort       = Set (Tuple [uninterpretedAtom, uninterpretedAtom])
    , isOriginal = False
    , arguments  = []
    }

univInt :: SmtDeclaration
univInt = SmtVariable { name       = "univInt"
                      , sort       = Set (Tuple [uninterpretedUInt])
                      , isOriginal = False
                      , arguments  = []
                      }

idenInt :: SmtDeclaration
idenInt = SmtVariable
    { name       = "idenInt"
    , sort       = Set (Tuple [uninterpretedUInt, uninterpretedUInt])
    , isOriginal = False
    , arguments  = []
    }

intValue :: SmtDeclaration
intValue = SmtVariable { name       = "intValue"
                       , sort       = SmtInt
                       , isOriginal = False
                       , arguments  = [uninterpretedUInt]
                       }

smtType :: SmtExpr -> Sort
smtType (SmtIntConstant  _               ) = SmtInt
smtType (SmtBoolConstant _               ) = SmtBool
smtType (SmtVar          SmtVariable {..}) = sort
smtType (SmtVar (SortDeclaration x)) =
    error ("Sort declaration " ++ (show x) ++ " is not an expression")
-- unary
smtType (SmtUnary Not        _     ) = SmtBool
smtType (SmtUnary Complement x     ) = smtType x
smtType (SmtUnary Transpose  _     ) = undefined
smtType (SmtUnary TClosure   x     ) = smtType x
smtType (SmtUnary Singleton  x     ) = Set (smtType x)
smtType (SmtUnary UnivSet    x     ) = smtType x
smtType (SmtUnary EmptySet   x     ) = smtType x
-- binary
smtType (SmtBinary Implies      _ _) = SmtBool
smtType (SmtBinary Plus         _ _) = SmtInt
smtType (SmtBinary Minus        _ _) = SmtInt
smtType (SmtBinary Multiply     _ _) = SmtInt
smtType (SmtBinary Divide       _ _) = SmtInt
smtType (SmtBinary Mod          _ _) = SmtInt
smtType (SmtBinary Eq           _ _) = SmtBool
smtType (SmtBinary Gte          _ _) = SmtBool
smtType (SmtBinary Lte          _ _) = SmtBool
smtType (SmtBinary Gt           _ _) = SmtBool
smtType (SmtBinary Lt           _ _) = SmtBool
smtType (SmtBinary Union        x _) = smtType x
smtType (SmtBinary Intersection x _) = smtType x
smtType (SmtBinary SetMinus     x _) = smtType x
smtType (SmtBinary Member       _ _) = SmtBool
smtType (SmtBinary Subset       _ _) = SmtBool
smtType (SmtBinary Join         x y) = smtJoinType (smtType x) (smtType y)
smtType (SmtBinary Product      x y) = case (xType, yType) of
    (Set (Tuple xs), Set (Tuple ys)) -> Set (Tuple (xs ++ ys))
    _ -> error ("Invalid product of " ++ (show xType) ++ " " ++ (show yType))
  where
    xType = smtType x
    yType = smtType y
smtType (SmtBinary TupSel _ _) = undefined
-- if then else
smtType (SmtIte    _      x _) = smtType x
-- quantified expression
smtType (SmtQt     _      _ _) = SmtBool
-- let expression
smtType (SmtLet _ x          ) = smtType x
smtType x = error ("type of " ++ (show x) ++ " is not implemented")

checkType :: SmtExpr -> Bool
checkType (SmtIntConstant  _    ) = True
checkType (SmtVar          _    ) = True
checkType (SmtBoolConstant _    ) = True
-- unary
checkType (SmtUnary Not        x) = (smtType x) == SmtBool
checkType (SmtUnary Complement x) = isSet (smtType x)
checkType (SmtUnary Transpose  x) = isRelation (smtType x)
checkType (SmtUnary TClosure   x) = isBinaryRelation (smtType x)
checkType (SmtUnary Singleton  _) = True
checkType (SmtUnary UnivSet    x) = isSortExpr x
checkType (SmtUnary EmptySet   x) = isSortExpr x
-- binary
checkType (SmtBinary Implies x y) =
    (smtType x) == SmtBool && (smtType y) == SmtBool
checkType (SmtBinary Plus x y) = (smtType x) == SmtInt && (smtType y) == SmtInt
checkType (SmtBinary Minus x y) =
    (smtType x) == SmtInt && (smtType y) == SmtInt
checkType (SmtBinary Multiply x y) =
    (smtType x) == SmtInt && (smtType y) == SmtInt
checkType (SmtBinary Divide x y) =
    (smtType x) == SmtInt && (smtType y) == SmtInt
checkType (SmtBinary Mod x y) = (smtType x) == SmtInt && (smtType y) == SmtInt
checkType (SmtBinary Eq  x y) = (smtType x) == SmtBool && (smtType y) == SmtBool
checkType (SmtBinary Gte x y) =
    (smtType x) == SmtBool && (smtType y) == SmtBool
checkType (SmtBinary Lte x y) =
    (smtType x) == SmtBool && (smtType y) == SmtBool
checkType (SmtBinary Gt x y) = (smtType x) == SmtBool && (smtType y) == SmtBool
checkType (SmtBinary Lt x y) = (smtType x) == SmtBool && (smtType y) == SmtBool

checkType (SmtBinary Union x y) = smtType x == smtType y && (isSet (smtType x))
checkType (SmtBinary Intersection x y) =
    smtType x == smtType y && (isSet (smtType x))
checkType (SmtBinary SetMinus x y) =
    smtType x == smtType y && (isSet (smtType x))
checkType (SmtBinary Member x y) = case (xType, smtType y) of
    (s1, (Set s2)) -> s1 == s2
    _              -> False
    where xType = smtType x
checkType (SmtBinary Subset x y) =
    smtType x == smtType y && (isSet (smtType x))
checkType (SmtBinary Join _ _) = undefined
checkType (SmtBinary Product x y) =
    isRelation (smtType x) && isRelation (smtType y)
checkType (SmtBinary TupSel _ _   ) = undefined
-- if then else
checkType (SmtIte    _      x y   ) = smtType x == smtType y
-- quantified expression
checkType (SmtQt     _      _ body) = smtType body == SmtBool
-- let expression
checkType (SmtLet _ _             ) = undefined
checkType x = error ("checkType of " ++ (show x) ++ " is not implemented")

isSet :: Sort -> Bool
isSet (Set _) = True
isSet _       = False

isRelation :: Sort -> Bool
isRelation (Set (Tuple _)) = True
isRelation _               = False

isBinaryRelation :: Sort -> Bool
isBinaryRelation (Set (Tuple (_ : (_ : [])))) = True
isBinaryRelation _                            = False

isTuple :: Sort -> Bool
isTuple (Tuple _) = True
isTuple _         = False

isSortExpr :: SmtExpr -> Bool
isSortExpr (SortExpr _) = True
isSortExpr _            = False

getElementSort :: Sort -> Sort
getElementSort (Set x) = x
getElementSort x       = error ("Expected a set. Found " ++ (show x))

--             old     -> new     -> body
replaceExpr :: SmtExpr -> SmtExpr -> SmtExpr -> SmtExpr
replaceExpr old new expr = if old == expr
    then new
    else case expr of
        SmtIntConstant  n -> SmtIntConstant n
        SmtBoolConstant x -> SmtBoolConstant x
        SmtVar          x -> SmtVar x
        SmtUnary op x     -> SmtUnary op (replaceExpr old new x)
        SmtBinary op x y ->
            SmtBinary op (replaceExpr old new x) (replaceExpr old new y)
        SmtIte c x y -> SmtIte (replaceExpr old new c)
                               (replaceExpr old new x)
                               (replaceExpr old new y)
        SmtLet _ _         -> error ("Unsupported") -- review this
        SmtQt qt vars body -> SmtQt qt vars (replaceExpr old new body) -- review this
        SortExpr sort      -> SortExpr sort
        SmtMultiArity op exprs ->
            SmtMultiArity op (map (replaceExpr old new) exprs)
        SmtCall function args ->
            SmtCall function (map (replaceExpr old new) args)

smtJoinType :: Sort -> Sort -> Sort
smtJoinType (Set (Tuple xs)) (Set (Tuple ys)) =
    Set (Tuple ((excludeLast xs) ++ (excludeFirst ys)))
smtJoinType x y = error ("Join Error: " ++ show (x, y))

-- SmtInt | SmtBool | Atom | UInt | Tuple [Sort] | Set Sort
makeRelation :: SmtExpr -> SmtExpr
makeRelation x = case smtType x of
    Set (Tuple _)         -> x
    UninterpretedSort _ _ -> SmtUnary Singleton (SmtMultiArity MkTuple [x])
    Tuple _               -> SmtUnary Singleton x
    _                     -> error ((show x) ++ " is not a relation")


concatSmtTuples :: SmtExpr -> SmtExpr -> SmtExpr
concatSmtTuples x y = case (smtType x, smtType y) of
    (Tuple xs, Tuple ys) -> SmtMultiArity MkTuple (xTuple ++ yTuple)
      where
        xTuple = map (\n -> SmtBinary TupSel (SmtIntConstant n) x)
                     [0 .. ((length xs) - 1)]
        yTuple = map (\n -> SmtBinary TupSel (SmtIntConstant n) y)
                     [0 .. ((length ys) - 1)]
    (_, _) -> error "Expected tuples"

