{-# LANGUAGE RecordWildCards #-}
module SmtLibPrinter where

import           SmtOperators
import           Smt
import           Env

prelude :: String
prelude = unlines
  [ "(set-logic ALL)"
  , "(set-option :tlimit 30000)"
  , "(set-option :block-models literals)"
  , "(set-option :finite-model-find true)"
  , "(set-option :produce-models true)"
  , "(set-option :incremental true)"
  , "(set-option :sets-ext true)"
  ]

printSmtLibScript :: Env -> String
printSmtLibScript RootEnv {..} =
  prelude
    ++ (concatMap declareSmtLibSort sorts)
    ++ (concatMap declareSmtLibConstants declarations)
    ++ (concatMap printSmtLibAssert assertions)
    ++ "(check-sat)\n"
    ++ "(get-model)\n"
printSmtLibScript _ = error "Expects a root environment here"

declareSmtLibSort :: Sort -> String
declareSmtLibSort (UninterpretedSort x y) =
  "(declare-sort " ++ x ++ " " ++ (show y) ++ ") \n"
declareSmtLibSort _ = error ("Invalid sort  declaration")

declareSmtLibConstants :: SmtDeclaration -> String
declareSmtLibConstants SmtVariable {..} =
  "(declare-const "
    ++ (printVariableName SmtVariable { .. })
    ++ " "
    ++ (printSmtLibSort sort)
    ++ " ) \n"
declareSmtLibConstants _ = error "Not a constant"

printSmtLibSort :: Sort -> String
printSmtLibSort s = case s of
  SmtInt                -> "Int"
  SmtBool               -> "Bool"
  UninterpretedSort x _ -> x
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

printVariableName :: SmtDeclaration -> String
printVariableName SmtVariable {..} =
  if isOriginal then ("|" ++ name ++ " |") else name
printVariableName (SortDeclaration _) = error "Expect SmtVariable"


printSmtLibVariable :: SmtDeclaration -> String
printSmtLibVariable SmtVariable {..} = "(" ++ varName ++ " " ++ varSort ++ ")"
 where
  varName = if isOriginal then ("|" ++ name ++ " |") else name
  varSort = printSmtLibSort sort
printSmtLibVariable (SortDeclaration _) = error "Expect SmtVariable"


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
