{-# LANGUAGE RecordWildCards #-}
module Smt where

import           SmtOperators

data SmtScript
    = SmtScript
    {
        sorts :: [Sort],
        constants :: [SmtVariable],
        assertions :: [Assertion]
    } deriving (Show, Eq)

emptySmtScript :: SmtScript
emptySmtScript = SmtScript { sorts = [], constants = [], assertions = [] }

addSort :: Sort -> SmtScript -> SmtScript
addSort s smtScript = smtScript { sorts = s : sorts smtScript }

getConstant :: SmtScript -> String -> SmtVariable
getConstant smtScript x = getByName (constants smtScript) x
  where
    getByName (v : vs) n = if name v == n then v else getByName vs n
    getByName _        n = error (n ++ " not found")

containsConstant :: SmtScript -> String -> Bool
containsConstant SmtScript {..} x =
    any (\SmtVariable {..} -> x == name) constants

addConstant :: SmtScript -> SmtVariable -> SmtScript
addConstant smtScript f = smtScript { constants = f : constants smtScript }

addConstants :: SmtScript -> [SmtVariable] -> SmtScript
addConstants = foldl addConstant

addAssertion :: SmtScript -> Assertion -> SmtScript
addAssertion smtScript a = smtScript { assertions = a : assertions smtScript }


addAssertions :: SmtScript -> [Assertion] -> SmtScript
addAssertions = foldl addAssertion

data SmtVariable
    = SmtVariable
    {
        name :: String,
        sort :: Sort,
        isOriginal :: Bool -- is it original smtScript name or auxiliary name?
    } deriving (Eq)

instance Show SmtVariable where
    show = name

data SmtExpr
    = SmtIntConstant Int
    | SmtVar SmtVariable
    | SmtBoolConstant Bool
    | SmtUnary SmtUnaryOp SmtExpr
    | SmtBinary SmtBinaryOp SmtExpr SmtExpr
    | SmtIte SmtExpr SmtExpr SmtExpr
    | SmtLet SmtVariable SmtExpr SmtExpr
    | SmtQt SmtQuantifier [SmtVariable] SmtExpr
    | SortExpr Sort
    | SmtMultiArity SmtMultiArityOp [SmtExpr]
    deriving (Show, Eq)

smtTrue :: SmtExpr
smtTrue = SmtBoolConstant True

smtFalse :: SmtExpr
smtFalse = SmtBoolConstant False

data Sort = SmtInt | SmtBool | Atom | UInt | Tuple [Sort] | Set Sort deriving (Show, Eq)

data Assertion = Assertion String SmtExpr deriving (Show, Eq)

none :: SmtVariable
none =
    SmtVariable { name = "none", sort = Set (Tuple [Atom]), isOriginal = False }

univAtom :: SmtVariable
univAtom = SmtVariable { name       = "univAtom"
                       , sort       = Set (Tuple [Atom])
                       , isOriginal = False
                       }

idenAtom :: SmtVariable
idenAtom = SmtVariable { name       = "idenAtom"
                       , sort       = Set (Tuple [Atom, Atom])
                       , isOriginal = False
                       }

univInt :: SmtVariable
univInt = SmtVariable { name       = "univInt"
                      , sort       = Set (Tuple [UInt])
                      , isOriginal = False
                      }

smtType :: SmtExpr -> Sort
smtType (SmtIntConstant  _               ) = SmtInt
smtType (SmtBoolConstant _               ) = SmtBool
smtType (SmtVar          SmtVariable {..}) = sort
-- unary
smtType (SmtUnary Not        _           ) = SmtBool
smtType (SmtUnary Complement x           ) = smtType x
smtType (SmtUnary Transpose  _           ) = undefined
smtType (SmtUnary TClosure   x           ) = smtType x
smtType (SmtUnary Singleton  x           ) = Set (smtType x)
smtType (SmtUnary UnivSet    x           ) = smtType x
smtType (SmtUnary EmptySet   x           ) = smtType x
-- binary
smtType (SmtBinary Implies      _ _      ) = SmtBool
smtType (SmtBinary Plus         _ _      ) = SmtInt
smtType (SmtBinary Minus        _ _      ) = SmtInt
smtType (SmtBinary Multiply     _ _      ) = SmtInt
smtType (SmtBinary Divide       _ _      ) = SmtInt
smtType (SmtBinary Mod          _ _      ) = SmtInt
smtType (SmtBinary Eq           _ _      ) = SmtBool
smtType (SmtBinary Gte          _ _      ) = SmtBool
smtType (SmtBinary Lte          _ _      ) = SmtBool
smtType (SmtBinary Gt           _ _      ) = SmtBool
smtType (SmtBinary Lt           _ _      ) = SmtBool
smtType (SmtBinary Union        x _      ) = smtType x
smtType (SmtBinary Intersection x _      ) = smtType x
smtType (SmtBinary SetMinus     x _      ) = smtType x
smtType (SmtBinary Member       _ _      ) = SmtBool
smtType (SmtBinary Subset       _ _      ) = SmtBool
smtType (SmtBinary Join         _ _      ) = undefined
smtType (SmtBinary Product      x y      ) = case (xType, yType) of
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
smtType (SmtLet    _      _ x) = smtType x
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
checkType (SmtLet    _      _ _   ) = undefined
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
