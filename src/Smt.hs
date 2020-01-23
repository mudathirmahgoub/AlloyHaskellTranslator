{-# LANGUAGE RecordWildCards #-}
module Smt where

import           SmtOperators

data SmtProgram
    = SmtProgram
    {
        sorts :: [Sort],
        constants :: [Variable],
        assertions :: [Assertion]
    } deriving (Show, Eq)

emptyProgram = SmtProgram { sorts = [], constants = [], assertions = [] }

addSort :: Sort -> SmtProgram -> SmtProgram
addSort s p = p { sorts = s : sorts p }

getConstant :: SmtProgram -> String -> Variable
getConstant p x = getByName (constants p) x
  where
    getByName (f : fs) x = if name f == x then f else getByName fs x
    getByName _        x = error (x ++ " not found")

addConstant :: SmtProgram -> Variable -> SmtProgram
addConstant p f = p { constants = f : constants p }

addConstants :: SmtProgram -> [Variable] -> SmtProgram
addConstants = foldl addConstant

addAssertion :: Assertion -> SmtProgram -> SmtProgram
addAssertion a p = p { assertions = a : assertions p }

data Variable
    = Variable
    {
        name :: String,
        sort :: Sort,
        isOriginal :: Bool -- is it original smt name or auxiliary name?
    } deriving (Eq)

instance Show Variable where
    show = name

data SmtExpr
    = SmtIntConstant Int
    | Var Variable
    | SmtBoolConstant Bool
    | SmtUnary SmtUnaryOp SmtExpr
    | SmtBinary SmtBinaryOp SmtExpr SmtExpr
    | SmtIte SmtExpr SmtExpr SmtExpr
    | SmtLet Variable SmtExpr SmtExpr
    | SmtQt SmtQuantifier [Variable] SmtExpr
    | SortExpr Sort
    | SmtMultiArity SmtMultiArityOp [SmtExpr]
    deriving (Show, Eq)

smtTrue = SmtBoolConstant True
smtFalse = SmtBoolConstant False

data Sort = SmtInt | SmtBool | Atom | UInt | Tuple [Sort] | Set Sort deriving (Show, Eq)

data Assertion = Assertion String SmtExpr deriving (Show, Eq)


none =
    Variable { name = "none", sort = Set (Tuple [Atom]), isOriginal = False }

univAtom = Variable { name       = "univAtom"
                    , sort       = Set (Tuple [Atom])
                    , isOriginal = False
                    }

idenAtom = Variable { name       = "idenAtom"
                    , sort       = Set (Tuple [Atom, Atom])
                    , isOriginal = False
                    }

univInt =
    Variable { name = "univInt", sort = Set (Tuple [UInt]), isOriginal = False }


smtType :: SmtExpr -> Sort
smtType (Var Variable {..}         ) = sort
-- unary
smtType (SmtUnary Not        _     ) = SmtBool
smtType (SmtUnary Complement x     ) = smtType x
smtType (SmtUnary Transpose  x     ) = undefined
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
smtType (SmtBinary Join         x y) = undefined
smtType (SmtBinary Product      x y) = case (xType, yType) of
    (Set (Tuple xs), Set (Tuple ys)) -> Set (Tuple (xs ++ ys))
    _ -> error ("Invalid product of " ++ (show xType) ++ " " ++ (show yType))
  where
    xType = smtType x
    yType = smtType y
smtType (SmtBinary TupSel x y) = undefined
-- if then else
smtType (SmtIte    _      x _) = smtType x
-- quantified expression
smtType (SmtQt     _      _ _) = SmtBool
-- let expression
smtType (SmtLet    _      _ x) = smtType x
