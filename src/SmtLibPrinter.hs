{-# LANGUAGE RecordWildCards #-}
module SmtLibPrinter where

import           SmtOperators
import           Smt

prelude = unlines
  [ "(set-logic ALL)"
  , "(set-option :tlimit 30000)"
  , "(set-option :block-models literals)"
  , "(set-option :finite-model-find true)"
  , "(set-option :produce-models true)"
  , "(set-option :incremental true)"
  , "(set-option :sets-ext true)"
  , "(declare-sort Atom 0)"
  , "(declare-sort UInt 0)"
  ]

printSmtLibScript :: SmtScript -> String
printSmtLibScript SmtScript {..} =
  prelude
    ++ (concatMap declareSmtLibSort sorts)
    ++ (concatMap declareSmtLibConstants constants)
    ++ (concatMap printSmtLibAssert assertions)

declareSmtLibSort :: Sort -> String
declareSmtLibSort s = "(declare-sort " ++ (show s) ++ " 0) \n"

declareSmtLibConstants :: SmtVariable -> String
declareSmtLibConstants SmtVariable {..} =
  "(declare-const "
    ++ (printVariableName SmtVariable { .. })
    ++ " "
    ++ (printSmtLibSort sort)
    ++ " ) \n"

printSmtLibSort :: Sort -> String
printSmtLibSort s = case s of
  SmtInt  -> "Int"
  SmtBool -> "Bool"
  Atom    -> "Atom"
  UInt    -> "UInt"
  Tuple sorts ->
    "(Tuple " ++ (concatMap (\x -> (printSmtLibSort x) ++ " ") sorts) ++ ")"
  Set sort -> "(Set " ++ (printSmtLibSort sort) ++ ")"

printSmtLibAssert :: Assertion -> String
printSmtLibAssert (Assertion comment expr) =
  ";" ++ comment ++ "\n" ++ "(assert " ++ (printSmtLibExpr expr) ++ ")\n"


printSmtLibExpr :: SmtExpr -> String
printSmtLibExpr (SmtIntConstant  x) = (show x)
printSmtLibExpr (SmtVar          x) = printVariableName x
printSmtLibExpr (SmtBoolConstant x) = if x then "true" else "false"
printSmtLibExpr (SmtUnary op x) =
  "(" ++ (printSmtLibUnaryOp op) ++ " " ++ (printSmtLibExpr x) ++ ")"
printSmtLibExpr (SmtBinary op x y) =
  "("
    ++ (printSmtLibBinaryOp op)
    ++ " "
    ++ (printSmtLibExpr x)
    ++ " "
    ++ (printSmtLibExpr y)
    ++ ")"
printSmtLibExpr (SmtIte x y z) =
  "(ite "
    ++ (printSmtLibExpr x)
    ++ " "
    ++ (printSmtLibExpr y)
    ++ (printSmtLibExpr z)
    ++ ")"
printSmtLibExpr (SmtLet list x) =
  "(let (" ++ (concatMap printVarExpr list) ++ ")" ++ (printSmtLibExpr x) ++ ")"
 where
  printVarExpr (v, e) =
    "(" ++ (printVariableName v) ++ " " ++ (printSmtLibExpr e) ++ ")"
printSmtLibExpr (SmtQt quantifier list x) =
  "("
    ++ (printSmtLibQuantifier quantifier)
    ++ "("
    ++ (concatMap printSmtLibVariable list)
    ++ ")"
    ++ (printSmtLibExpr x)
    ++ ")"
printSmtLibExpr (SortExpr sort       ) = printSmtLibSort sort
printSmtLibExpr (SmtMultiArity And []) = "true"
printSmtLibExpr (SmtMultiArity op xs) =
  "("
    ++ (printSmtLibMultiArityOp op)
    ++ " "
    ++ (concatMap printSmtLibExpr xs)
    ++ ")"

printVariableName :: SmtVariable -> String
printVariableName SmtVariable {..} =
  if isOriginal then ("|" ++ name ++ " |") else name


printSmtLibVariable :: SmtVariable -> String
printSmtLibVariable SmtVariable {..} = "(" ++ varName ++ " " ++ varSort ++ ")"
 where
  varName = if isOriginal then ("|" ++ name ++ " |") else name
  varSort = printSmtLibSort sort

printSmtLibUnaryOp :: SmtUnaryOp -> String
printSmtLibUnaryOp op = case op of
  Not        -> "not"
  Complement -> "complement"
  Transpose  -> "transpose"
  TClosure   -> "tclosure"
  Singleton  -> "singleton"
  UnivSet    -> "as univset"
  EmptySet   -> "as emptyset"


printSmtLibBinaryOp :: SmtBinaryOp -> String
printSmtLibBinaryOp op = case op of
  Implies      -> "=>"
  Plus         -> "+"
  Minus        -> "-"
  Multiply     -> "*"
  Divide       -> "/"
  Mod          -> "mod"
  Eq           -> "="
  Gte          -> ">="
  Lte          -> "<="
  Gt           -> ">"
  Lt           -> "<"
  Union        -> "union"
  Intersection -> "intersection"
  SetMinus     -> "setminus"
  Member       -> "member"
  Subset       -> "subset"
  Join         -> "join"
  Product      -> "product"
  TupSel       -> "tupSel"

printSmtLibMultiArityOp :: SmtMultiArityOp -> String
printSmtLibMultiArityOp op = case op of
  MkTuple  -> "mkTuple"
  Insert   -> "insert"
  Distinct -> "distinct"
  And      -> "and"
  Or       -> "or"

printSmtLibQuantifier :: SmtQuantifier -> String
printSmtLibQuantifier q = case q of
  Exists -> "exists"
  ForAll -> "forall"
