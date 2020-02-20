{-# LANGUAGE RecordWildCards #-}
module Translator where
import           AlloyOperators
import           SmtOperators
import           Alloy
import           Smt
import           Env

translateModel :: AlloyModel -> Env
translateModel model = env6
 where
  sigs = signatures model
  env1 = declareSignatures emptyEnv sigs
  env2 = translateSignatures env1 sigs
  env3 = translateSignatureFacts env2 sigs
  env4 = translateFacts env3 (facts model)
  -- axioms for none, univAtom, univInt, intValue
  env5 = addSpecialAssertions env4
  env6 = translateCommands env5 (commands model)

translateSignatures :: Env -> [Sig] -> Env
translateSignatures env [] = env
translateSignatures env xs = translateHierarchy env (filter isTopLevel xs)

declareSignatures :: Env -> [Sig] -> Env
declareSignatures env xs = foldl declareSignature env xs

declareSignature :: Env -> Sig -> Env
declareSignature env Univ   = env
declareSignature env SigInt = env
declareSignature env None   = env
declareSignature _ SigString =
  error ("Strings are not supported yet in alloy.")
declareSignature env sig = addDeclaration
  env
  SmtVariable { name = label sig, sort = s, isOriginal = True, arguments = [] }
  where s = translateType (Prod [sig])

translateHierarchy :: Env -> [Sig] -> Env
translateHierarchy env xs = foldl translateSignature env xs

translateSignature :: Env -> Sig -> Env
translateSignature env Univ   = env
translateSignature env SigInt = env
translateSignature env None   = env
translateSignature _ SigString =
  error ("Strings are not supported yet in alloy.")
translateSignature env PrimSig {..} = env5
 where
  env0 = foldl translateSignature env children
  env1 = translateSigMultiplicity env0 PrimSig { .. }
  env2 = translateParent env1 PrimSig { .. }
  env3 = translateDisjointChildren env2 PrimSig { .. }
  env4 = translateAbstract env3 PrimSig { .. }
  env5 = translateFields env4 PrimSig { .. }

translateSignature env SubsetSig {..} = env3
 where
  env1 = translateSigMultiplicity env SubsetSig { .. }
  env2 = translateParent env1 SubsetSig { .. }
  env3 = translateFields env2 SubsetSig { .. }

-- require sig is already defined in SMTScript p
translateSigMultiplicity :: Env -> Sig -> Env
-- sig a
-- use different from empty set
translateSigMultiplicity env sig = addAssertion env assertion
 where
  c = getDeclaration env (label sig)
  s = case translateType (Prod [sig]) of
    Set (Tuple ((UninterpretedSort u arity) : [])) ->
      (UninterpretedSort u arity)
    _ -> error ("invalid sig sort " ++ (show s))
  x = SmtVariable { name = "x", sort = s, isOriginal = False, arguments = [] }
  singleton   = (SmtUnary Singleton (SmtMultiArity MkTuple [SmtVar x]))
  isSingleton = SmtBinary Eq (SmtVar c) singleton
  subset      = SmtBinary Subset singleton (SmtVar c)
  empty       = SmtUnary EmptySet (SortExpr (Set (Tuple [s])))
  isEmpty     = SmtBinary Eq empty (SmtVar c)
  existsOne   = SmtQt Exists [x] isSingleton
  existsSome  = SmtQt Exists [x] subset
  orExpr      = SmtMultiArity Or [existsOne, isEmpty]
  assertion   = case (multiplicity sig) of
    ONEOF  -> Assertion ("one " ++ (label sig)) existsOne
    LONEOF -> Assertion ("lone " ++ (label sig)) orExpr
    SOMEOF -> Assertion ("some " ++ (label sig)) existsSome
    _      -> Assertion "" smtTrue

-- refactor this with subset 
translateParent :: Env -> Sig -> Env
translateParent env PrimSig {..} = addAssertion env assertion
 where
  childVar  = getDeclaration env primLabel
  parentVar = getDeclaration env (label parent)
  subset    = SmtBinary Subset (SmtVar childVar) (SmtVar parentVar)
  assertion = Assertion ("parent " ++ primLabel) subset

translateParent env SubsetSig {..} = addAssertion env assertion
 where
  childVar   = getDeclaration env subsetLabel
  parentVars = map (getDeclaration env . label) parents
  function parentVar = SmtBinary Subset (SmtVar childVar) (SmtVar parentVar)
  subsets   = SmtMultiArity And (map function parentVars)
  assertion = Assertion ("parents " ++ subsetLabel) subsets

translateParent _ _ = undefined


translateDisjointChildren :: Env -> Sig -> Env
translateDisjointChildren env PrimSig {..} = addAssertion env assertion
 where
  function (x, y) = SmtBinary
    Eq
    empty
    (SmtBinary Intersection (SmtVar xVar) (SmtVar yVar))
   where
    xVar = getDeclaration env (label x)
    yVar = getDeclaration env (label y)
  disjointChildren zs = map function zs
  sigSort   = translateType (Prod [PrimSig { .. }])
  empty     = SmtUnary EmptySet (SortExpr sigSort)
  pairs     = [ (u, v) | u <- children, v <- children, (label u) < (label v) ]
  andExpr   = SmtMultiArity And (disjointChildren pairs)
  assertion = Assertion ("disjoint children of " ++ primLabel) andExpr
translateDisjointChildren _ sig =
  error ((label sig) ++ " is not a prime signature")

translateAbstract :: Env -> Sig -> Env
translateAbstract env PrimSig {..} = case isAbstract && not (null children) of
  False -> env
  True  -> addAssertion env assertion
   where
    function x y = SmtBinary Union x y
    sigVar    = getDeclaration env primLabel
    union     = foldl function empty variables
    variables = map (SmtVar . getDeclaration env . label) children
    empty     = SmtUnary EmptySet (SortExpr (sort sigVar))
    equal     = SmtBinary Eq (SmtVar sigVar) union
    assertion = Assertion ("abstract " ++ primLabel) equal
translateAbstract _ sig = error ((label sig) ++ " is not a prime signature")

translateFields :: Env -> Sig -> Env
translateFields env sig = env4
 where
  groups        = fields sig
  individuals   = splitDecls groups
  env1          = foldl (declareField sig) env individuals
  env2          = foldl (translateField sig) env1 individuals
  disjointExprs = translateDisjointDecls env2 groups
  env3 =
    addAssertion env2 (Assertion ("disjoint " ++ (show groups)) disjointExprs)
  env4 = translateDisjoint2Decls env3 individuals

declareField :: Sig -> Env -> Decl -> Env
declareField sig env Decl {..} = addDeclaration env constant
 where
  constant = SmtVariable { name       = concat (declNames Decl { .. })
                         , sort       = smtSort
                         , isOriginal = True
                         , arguments  = []
                         }
  smtSort = translateType (alloyType (AlloyBinary ARROW (Signature sig) expr))

translateField :: Sig -> Env -> Decl -> Env
-- Sig A {field: expr} is translated into 
-- (1) all this: A | let $s$ = this.field | $s$ in expr
-- (2) field in (A -> removeMultiplicity[expr]) where every occurence of 'this' in expr is replaced with A
-- Example: sig A { r: set A, s: r->some A }. No occurence of this in 'set A'. AlloyExpr 'r -> some A' 
-- is actually given as 'this . r -> some A'. I translate field s (with type Set Tuple[Atom, Atom, Atom])
-- as follows:
-- (1) (all this: A | (let $s$= this . s | $s$ in (this . r) ->some A))
-- (2) s in A -> (A . r) -> A
-- The second constraint is needed because A is not a type in smt, but a subset of Atoms. Without
-- this constraint, s can be in  B -> (A . r) -> A where B is another top level signature


translateField sig env Decl {..} = env2
 where
  fieldVar      = getDeclaration env (concat (declNames Decl { .. }))
  this          = AlloyVariable "this" (Prod [sig])
  thisExpr      = AlloyVar this
  thisJoinField = AlloyBinary JOIN thisExpr (Field Decl { .. })
  s             = AlloyVariable "s" (alloyType thisJoinField)
  sInExpr       = AlloyBinary IN (AlloyVar s) expr
  alloyLet      = AlloyLet s thisJoinField sInExpr
  decl          = Decl { names     = [this]
                       , expr      = AlloyUnary ONEOF (Signature sig)
                       , disjoint  = False
                       , disjoint2 = False
                       }
  allExpr         = AlloyQt All [decl] alloyLet
  smtMultiplicity = smtExpr
   where
    (_, smtExpr) = translate
      ( Env { auxiliaryFormula = Nothing, variablesMap = [], parent = env }
      , allExpr
      )
  multiplicityAssertion =
    Assertion ((show fieldVar) ++ " field multiplicity") smtMultiplicity
  noMuliplicity = removeMultiplicity expr
  substitution  = substitute this (Signature sig) noMuliplicity
  productExpr   = AlloyBinary ARROW (Signature sig) substitution
  subsetExpr    = AlloyBinary IN (Field Decl { .. }) productExpr
  env1 = translateFormula env ((show fieldVar) ++ " field subset") subsetExpr
  env2          = addAssertion env multiplicityAssertion

translateDisjointDecls :: Env -> [Decl] -> SmtExpr
translateDisjointDecls env decls =
  SmtMultiArity And (map (translateDisjointDecl env) decls)

translateDisjointDecl :: Env -> Decl -> SmtExpr
translateDisjointDecl env decl = andExpr
 where
  function (x, y) = SmtBinary
    Eq
    empty
    (SmtBinary Intersection (SmtVar xVar) (SmtVar yVar))
   where
    xVar  = getVariable env (alloyVarName x)
    yVar  = getVariable env (alloyVarName y)
    empty = SmtUnary EmptySet (SortExpr (sort xVar))
  pairs =
    [ (u, v)
    | u <- names decl
    , v <- names decl
    , (alloyVarName u) < (alloyVarName v)
    ]
  andExpr = SmtMultiArity And (map function pairs)


translateDisjoint2Decls :: Env -> [Decl] -> Env
translateDisjoint2Decls env _ = env -- ToDo: fix this

translateSignatureFacts :: Env -> [Sig] -> Env
translateSignatureFacts env [] = env
translateSignatureFacts env xs = foldl translateSignatureFact env xs

-- sig s{...}{expr} is translated into
-- {all this: s | expr}
translateSignatureFact :: Env -> Sig -> Env
translateSignatureFact env sig = case (sigfacts sig) of
  [] -> env
  _  -> env1   where
    sigVar       = getDeclaration env (label sig)
    env1         = addAssertion env assertion
    assertion    = Assertion ((show sigVar) ++ " sig facts") smtExpr
    (_, smtExpr) = translate
      ( Env { auxiliaryFormula = Nothing, variablesMap = [], parent = env }
      , allExpr
      )
    allExpr = AlloyQt All [decl] andExpr
    andExpr = AlloyList ListAND (sigfacts sig)
    this    = AlloyVariable "this" (Prod [sig])
    decl    = Decl { names     = [this]
                   , expr      = AlloyUnary ONEOF (Signature sig)
                   , disjoint  = False
                   , disjoint2 = False
                   }

translateFacts :: Env -> [Fact] -> Env
translateFacts env xs = foldl translateFact env xs

translateFact :: Env -> Fact -> Env
translateFact env (Fact name alloyExpr) = translateFormula env name alloyExpr

addSpecialAssertions :: Env -> Env
addSpecialAssertions env = env -- ToDo: change this later

translateCommands :: Env -> [Command] -> Env
translateCommands env xs = foldl translateCommand env xs

translateCommand :: Env -> Command -> Env
translateCommand _ _ = undefined

translateFormula :: Env -> String -> AlloyExpr -> Env
translateFormula env string alloyExpr = env2
 where
  (env1, smtExpr) = translate
    ( Env { auxiliaryFormula = Nothing, variablesMap = [], parent = env }
    , alloyExpr
    )
  formula   = translateAuxiliaryFormula env1 smtExpr
  assertion = Assertion string formula
  env2      = case env1 of
    Env {..} -> addAssertion parent assertion
    _        -> error "Expect Env{..}"

translateAuxiliaryFormula :: Env -> SmtExpr -> SmtExpr
translateAuxiliaryFormula Env { auxiliaryFormula = Nothing } expr = expr
translateAuxiliaryFormula Env { auxiliaryFormula = (Just aux) } expr =
  case aux of
    SmtQt Exists variables body ->
      SmtQt Exists variables (SmtMultiArity And [body, expr])
    SmtQt ForAll variables body ->
      SmtQt ForAll variables (SmtBinary Implies body expr)
    _ -> error ("Auxiliary formula " ++ (show aux) ++ " is not supported")

translate :: (Env, AlloyExpr) -> (Env, SmtExpr)
translate (env, Signature x) = (env, SmtVar (getDeclaration env (label x)))
translate (env, Field Decl {..}) =
  (env, SmtVar (getDeclaration env (getFieldName Decl { .. })))
translate (env, (AlloyConstant c sig)) = case sig of
  SigInt -> translateIntConstant env (read c)
  _      -> error ("Constant " ++ (show c) ++ " is not supported")
translate (env, AlloyVar x) = (env, SmtVar variable)
  where variable = getVariable env (alloyVarName x)
translate (_  , (AlloyUnary SOMEOF _)   ) = undefined
translate (_  , (AlloyUnary LONEOF _)   ) = undefined
translate (env, (AlloyUnary ONEOF x)    ) = translate (env, x)
translate (_  , (AlloyUnary SETOF _)    ) = undefined
translate (_  , (AlloyUnary EXACTLYOF _)) = undefined
translate (env, (AlloyUnary NOT x)) =
  (env, SmtUnary Not (second (translate (env, x))))
translate (_  , (AlloyUnary NO _)) = undefined
translate (env, AlloyUnary SOME x) = (env, someExpr)
 where
  someExpr        = translateAuxiliaryFormula env1 notEmpty
  (env1, setExpr) = translate (env, x)
  empty           = SmtUnary EmptySet (SortExpr (smtType setExpr))
  equal           = SmtBinary Eq empty setExpr
  notEmpty        = SmtUnary Not equal

translate (_, (AlloyUnary LONE _)     ) = undefined
translate (_, (AlloyUnary ONE _)      ) = undefined
translate (_, (AlloyUnary TRANSPOSE _)) = undefined
translate (_, (AlloyUnary RCLOSURE _) ) = undefined
translate (_, (AlloyUnary CLOSURE _)  ) = undefined
translate (_, (AlloyUnary CARDINALITY _)) =
  error ("Cardinality not supported here.")
translate (_  , AlloyUnary CAST2INT _   ) = undefined
translate (_  , AlloyUnary CAST2SIGINT _) = undefined
translate (env, (AlloyUnary NOOP x)     ) = translate (env, x)
-- binary expressions
translate (env, (AlloyBinary ARROW x y) ) = (env, SmtBinary Product a b)
 where
  (_, a) = translate (env, x)
  (_, b) = translate (env, y)

translate (_  , (AlloyBinary ANY_ARROW_SOME _ _)  ) = undefined
translate (_  , (AlloyBinary ANY_ARROW_ONE _ _)   ) = undefined
translate (_  , (AlloyBinary ANY_ARROW_LONE _ _)  ) = undefined
translate (_  , (AlloyBinary SOME_ARROW_ANY _ _)  ) = undefined
translate (_  , (AlloyBinary SOME_ARROW_SOME _ _) ) = undefined
translate (_  , (AlloyBinary SOME_ARROW_ONE _ _)  ) = undefined
translate (_  , (AlloyBinary SOME_ARROW_LONE _ _) ) = undefined
translate (_  , (AlloyBinary ONE_ARROW_ANY _ _)   ) = undefined
translate (_  , (AlloyBinary ONE_ARROW_SOME _ _)  ) = undefined
translate (_  , (AlloyBinary ONE_ARROW_ONE _ _)   ) = undefined
translate (_  , (AlloyBinary ONE_ARROW_LONE _ _)  ) = undefined
translate (_  , (AlloyBinary LONE_ARROW_ANY _ _)  ) = undefined
translate (_  , (AlloyBinary LONE_ARROW_SOME _ _) ) = undefined
translate (_  , (AlloyBinary LONE_ARROW_ONE _ _)  ) = undefined
translate (_  , (AlloyBinary LONE_ARROW_LONE _ _) ) = undefined
translate (_  , (AlloyBinary ISSEQ_ARROW_LONE _ _)) = undefined
translate (env, (AlloyBinary JOIN x y)) = (env, SmtBinary Join smtX smtY)
 where
  smtX = makeRelation (second (translate (env, x)))
  smtY = makeRelation (second (translate (env, y)))
translate (_, (AlloyBinary DOMAIN _ _)) = undefined
translate (_, (AlloyBinary RANGE _ _) ) = undefined
translate (env, (AlloyBinary INTERSECT x y)) =
  ( env
  , SmtBinary Intersection
              (second (translate (env, x)))
              (second (translate (env, y)))
  )
translate (_, (AlloyBinary PLUSPLUS _ _)) = undefined
translate (env, (AlloyBinary PLUS x y)) =
  ( env
  , SmtBinary Union (second (translate (env, x))) (second (translate (env, y)))
  )
translate (_, (AlloyBinary IPLUS _ _) ) = undefined
translate (_, (AlloyBinary MINUS _ _) ) = undefined
translate (_, (AlloyBinary IMINUS _ _)) = undefined
translate (_, (AlloyBinary MUL _ _)   ) = undefined
translate (_, (AlloyBinary DIV _ _)   ) = undefined
translate (_, (AlloyBinary REM _ _)   ) = undefined
translate (env, (AlloyBinary IMPLIES x y)) =
  ( env
  , SmtBinary Implies
              (second (translate (env, x)))
              (second (translate (env, y)))
  )

translate (env, (AlloyBinary Less x y)) =
  translateComparison (env, (AlloyBinary Less x y))
translate (env, (AlloyBinary LTE x y)) =
  translateComparison (env, (AlloyBinary LTE x y))
translate (env, (AlloyBinary Greater x y)) =
  translateComparison (env, (AlloyBinary Greater x y))
translate (env, (AlloyBinary GTE x y)) =
  translateComparison (env, (AlloyBinary GTE x y))
translate (env, (AlloyBinary NOT_LT x y)) =
  translateComparison (env, (AlloyBinary NOT_LT x y))
translate (env, (AlloyBinary NOT_LTE x y)) =
  translateComparison (env, (AlloyBinary NOT_LTE x y))
translate (env, (AlloyBinary NOT_GT x y)) =
  translateComparison (env, (AlloyBinary NOT_GT x y))
translate (env, (AlloyBinary NOT_GTE x y)) =
  translateComparison (env, (AlloyBinary NOT_GTE x y))
translate (env, (AlloyBinary EQUALS x y)) =
  translateComparison (env, (AlloyBinary EQUALS x y))
translate (env, (AlloyBinary NOT_EQUALS x y)) =
  translateComparison (env, (AlloyBinary NOT_EQUALS x y))

translate (_  , (AlloyBinary SHL _ _)) = undefined
translate (_  , (AlloyBinary SHA _ _)) = undefined
translate (_  , (AlloyBinary SHR _ _)) = undefined

-- Translation of 'x in y' where A = translate x, B = translate Y
-- left sort | right sort | Translation
-- -------------------------------------
-- tuple     | tuple      | (= A B)
-- tuple     | set        | (member tuple set)
-- set       | set        | (subset A B)
translate (env, (AlloyBinary IN x y) ) = (env, auxiliaryB)
 where
  smtIn     = memberOrSubset a b (smtType a) (smtType b)
  (envA, a) = translate (env, x)
  (envB, b) = translate (env, y)
  memberOrSubset u v (Tuple _) (Tuple _) = SmtBinary Eq u v -- not sure this occurs        
  memberOrSubset u v (Tuple _) (Set   _) = SmtBinary Member u v
  memberOrSubset u v (Set   _) (Set   _) = SmtBinary Subset u v
  memberOrSubset u v _ (Set _) = SmtBinary Member (SmtMultiArity MkTuple [u]) v
  memberOrSubset u v _ _ =
    error ("Invalid operation: " ++ (show u) ++ " in " ++ (show v))
  auxiliaryA = translateAuxiliaryFormula envA smtIn
  auxiliaryB = case auxiliaryFormula envB of
    Nothing                   -> auxiliaryA
    Just (SmtQt Exists _ aux) -> replaceExpr b a aux -- ToDo: review this (important)
    _                         -> error ("This should never happen")

translate (env, (AlloyBinary NOT_IN x y)) = (env, SmtUnary Not expr)
  where (_, expr) = translate (env, AlloyBinary IN x y)
translate (env, (AlloyBinary AND x y)) =
  ( env
  , SmtMultiArity
    And
    [(second (translate (env, x))), (second (translate (env, y)))]
  )
translate (env, (AlloyBinary OR x y)) =
  ( env
  , SmtMultiArity
    Or
    [(second (translate (env, x))), (second (translate (env, y)))]
  )
translate (env, (AlloyBinary IFF x y)) =
  ( env
  , SmtBinary Eq (second (translate (env, x))) (second (translate (env, y)))
  )
-- if then else expression
translate (env, (AlloyITE c x y)) =
  ( env
  , SmtIte (second (translate (env, c)))
           (second (translate (env, x)))
           (second (translate (env, y)))
  )
-- quantified expression
-- all x: some A| all y: one x | some y
-- check with Andy with quantifiers versus nested quantifiers
translate (env, (AlloyQt op decls body)) = (env2, smtQt)
 where
  variableTuples   = map (translateDecl env) (splitDecls decls)
  variables        = map first variableTuples
  rangeConstraints = concat (map second variableTuples)
  env1             = addVariables env variables
  disjoint         = translateDisjointDecls env1 decls
  constraints      = SmtMultiArity And (disjoint : rangeConstraints)
  (env2, bodyExpr) = translate (env1, body)
  smtQt            = translateQt op
  translateQt All = case auxiliaryFormula env2 of
    Nothing -> SmtQt ForAll variables (SmtBinary Implies constraints bodyExpr)
    Just (SmtQt Exists existsVars existsBody) -> SmtQt
      ForAll
      variables
      (SmtBinary Implies constraints newBody)
     where
      newBody =
        (SmtQt Exists existsVars (SmtMultiArity And [existsBody, bodyExpr]))
    Just x ->
      error ("Do not know how to translate auxiliary formula: " ++ (show x))
  translateQt No            = SmtUnary Not (translateQt All)
  translateQt Lone          = undefined
  translateQt Some          = undefined
  translateQt Sum           = undefined
  translateQt Comprehension = undefined
  translateQt _             = error ((show op) ++ " is not an alloy quantifier")


-- let expression
translate (env, (AlloyLet var alloyExpr body)) = (env3, smtLet)
 where
  smtVar          = SmtVariable (alloyVarName var) (smtType smtExpr) True []
  (env1, smtExpr) = translate (env, alloyExpr)
  env2            = addVariable env1 smtVar
  (env3, smtBody) = translate (env2, body)
  smtLet          = SmtLet [(smtVar, smtExpr)] smtBody

translate (env, AlloyList op xs) = case op of
  ListAND -> (env, SmtMultiArity And exprs)
    where exprs = map second (map (\x -> translate (env, x)) xs)
  ListOR     -> undefined
  TOTALORDER -> undefined
  DISJOINT   -> undefined


-- types
translateType :: AlloyType -> Sort
translateType (Prod xs) = Set (Tuple ys)
 where
  ys = map
    (\x -> if isInt (Signature x) then uninterpretedUInt else uninterpretedAtom)
    xs
translateType AlloyBool = SmtBool



-- SmtExpr for multiplicity and range constraints
-- ToDo: optimize this such that this is called once for Decl like (x, y : expr)    
translateDecl :: Env -> Decl -> (SmtDeclaration, [SmtExpr])
translateDecl env decl = (var, exprs)
 where
  varName      = concat (declNames decl)
  (var, exprs) = translateDeclExpr (env, expr decl)
  translateDeclExpr (env, AlloyUnary ONEOF x) = (variable, [member])
   where
    (_, smtExpr) = translate (env, x)
    varSort      = case (smtType smtExpr) of
      Set (Tuple (y : [])) -> Tuple (y : []) -- arity 1
      s -> error ("Expected a relation with arity 1. Found " ++ (show s))
    variable = SmtVariable { name       = varName
                           , sort       = varSort
                           , isOriginal = True
                           , arguments  = []
                           }
    member = SmtBinary Member (SmtVar variable) smtExpr

  translateDeclExpr (env, AlloyUnary SOMEOF x) = (variable, [subset, notEmpty])
   where
    (_, smtExpr) = translate (env, x)
    varSort      = smtType smtExpr
    variable     = SmtVariable { name       = varName
                               , sort       = varSort
                               , isOriginal = True
                               , arguments  = []
                               }
    subset   = SmtBinary Subset (SmtVar variable) smtExpr
    emptySet = SmtUnary EmptySet (SortExpr varSort)
    notEmpty = SmtUnary Not (SmtBinary Eq (SmtVar variable) emptySet)
  translateDeclExpr (env, AlloyUnary LONEOF x) = (variable, [subset, loneExpr])
   where
    (_, smtExpr) = translate (env, x)
    varSort      = smtType smtExpr
    variable     = SmtVariable { name       = varName
                               , sort       = varSort
                               , isOriginal = True
                               , arguments  = []
                               }
    subset      = SmtBinary Subset (SmtVar variable) smtExpr
    emptySet    = SmtUnary EmptySet (SortExpr varSort)
    empty       = SmtBinary Eq (SmtVar variable) emptySet
    elementSort = getElementSort varSort
    element     = SmtVariable { name       = varName ++ "Singleton"
                              , sort       = elementSort
                              , isOriginal = False
                              , arguments  = []
                              }
    singleton   = (SmtUnary Singleton (SmtMultiArity MkTuple [SmtVar element]))
    isSingleton = SmtBinary Eq (SmtVar variable) singleton
    existsExpr  = SmtQt Exists [element] subset
    loneExpr    = SmtMultiArity Or [empty, existsExpr]

  translateDeclExpr (env, AlloyUnary SETOF x) = (variable, [subset])
   where
    (_, smtExpr) = translate (env, x)
    varSort      = smtType smtExpr
    variable     = SmtVariable { name       = varName
                               , sort       = varSort
                               , isOriginal = True
                               , arguments  = []
                               }
    subset = SmtBinary Subset (SmtVar variable) smtExpr

  translateDeclExpr (_, AlloyBinary _ _ _) = undefined
  translateDeclExpr (_, x) = error ("Invalid decl expr: " ++ (show x))

translateComparison :: (Env, AlloyExpr) -> (Env, SmtExpr)

translateComparison (env, (AlloyBinary op (AlloyUnary CARDINALITY x) (AlloyConstant c SigInt)))
  = (env1, translateAuxiliaryFormula env1 smtExpr)
 where
  (env1, setExpr) = translate (env, x)
  n               = read c
  smtExpr         = translateCardinalityComparison env op setExpr n

translateComparison (env, (AlloyBinary op (AlloyConstant c SigInt) (AlloyUnary CARDINALITY x)))
  = case op of
    Less -> translateComparison
      ( env
      , (AlloyBinary Greater (AlloyUnary CARDINALITY x) (AlloyConstant c SigInt)
        )
      )
    LTE -> translateComparison
      ( env
      , (AlloyBinary GTE (AlloyUnary CARDINALITY x) (AlloyConstant c SigInt))
      )
    Greater -> translateComparison
      ( env
      , (AlloyBinary Less (AlloyUnary CARDINALITY x) (AlloyConstant c SigInt))
      )
    GTE -> translateComparison
      ( env
      , (AlloyBinary LTE (AlloyUnary CARDINALITY x) (AlloyConstant c SigInt))
      )
    NOT_LT -> translateComparison
      ( env
      , (AlloyBinary NOT_GT (AlloyUnary CARDINALITY x) (AlloyConstant c SigInt))
      )
    NOT_LTE -> translateComparison
      ( env
      , (AlloyBinary NOT_GTE (AlloyUnary CARDINALITY x) (AlloyConstant c SigInt)
        )
      )
    NOT_GT -> translateComparison
      ( env
      , (AlloyBinary NOT_LT (AlloyUnary CARDINALITY x) (AlloyConstant c SigInt))
      )
    NOT_GTE -> translateComparison
      ( env
      , (AlloyBinary NOT_LTE (AlloyUnary CARDINALITY x) (AlloyConstant c SigInt)
        )
      )
    EQUALS -> translateComparison
      ( env
      , (AlloyBinary EQUALS (AlloyUnary CARDINALITY x) (AlloyConstant c SigInt))
      )
    NOT_EQUALS -> translateComparison
      ( env
      , (AlloyBinary NOT_EQUALS
                     (AlloyUnary CARDINALITY x)
                     (AlloyConstant c SigInt)
        )
      )
    _ -> error "Invalid comparision operator"

-- general case for = , !=
translateComparison (env, (AlloyBinary EQUALS x y)) = (env2, smtExpr)
 where
  (env1, xExpr) = (translate (env, x))
  (env2, yExpr) = (translate (env1, y))
  equal         = SmtBinary Eq xExpr yExpr
  smtExpr       = translateAuxiliaryFormula env2 equal
translateComparison (env, (AlloyBinary NOT_EQUALS x y)) = (env1, smtExpr)
 where
  smtExpr       = SmtUnary Not equal
  (env1, equal) = translateComparison (env, (AlloyBinary EQUALS x y))


-- arithmetic
translateComparison (env, (AlloyBinary op x y)) =
  translateArithmetic (env, (AlloyBinary op x y))


translateCardinalityComparison
  :: Env -> AlloyBinaryOp -> SmtExpr -> Int -> SmtExpr
translateCardinalityComparison (Env {..}) op setExpr n = case op of
  Less -> case n of
    n | n <= 0    -> SmtBoolConstant False
    n | n == 1    -> isEmpty
    n | otherwise -> SmtQt Exists vars (SmtBinary Subset setExpr cardinalitySet)
     where
      vars           = generateVars (n - 1)
      cardinalitySet = generateSet vars
  LTE -> case n of
    n | n <= -1   -> SmtBoolConstant False
    n | n == 0    -> isEmpty
    n | otherwise -> SmtQt Exists vars (SmtBinary Subset setExpr cardinalitySet)
     where
      vars           = generateVars n
      cardinalitySet = generateSet vars
  Greater -> case n of
    n | n <= -1   -> SmtBoolConstant True
    n | otherwise -> SmtQt Exists vars (SmtBinary Subset cardinalitySet setExpr)
     where
      vars           = generateVars (n + 1)
      cardinalitySet = generateSet vars
  GTE -> case n of
    n | n <= 0    -> SmtBoolConstant True
    n | otherwise -> SmtQt Exists vars (SmtBinary Subset cardinalitySet setExpr)
     where
      vars           = generateVars n
      cardinalitySet = generateSet vars
  NOT_LT  -> translateCardinalityComparison Env { .. } GTE setExpr n
  NOT_LTE -> translateCardinalityComparison Env { .. } Greater setExpr n
  NOT_GT  -> translateCardinalityComparison Env { .. } LTE setExpr n
  NOT_GTE -> translateCardinalityComparison Env { .. } Less setExpr n
  EQUALS  -> case n of
    n | n <= -1   -> SmtBoolConstant False
    n | n == 0    -> isEmpty
    n | otherwise -> SmtQt Exists vars (SmtBinary Eq setExpr cardinalitySet)
     where
      vars           = generateVars (n - 1)
      cardinalitySet = generateSet vars
  NOT_EQUALS ->
    SmtUnary Not (translateCardinalityComparison Env { .. } EQUALS setExpr n)
  _ -> error "Invalid comparision operator"
 where
  setSort     = (smtType setExpr)
  emptySet    = SmtUnary EmptySet (SortExpr setSort)
  elementSort = case setSort of
    Set x -> x
    _     -> error ((show setSort) ++ " is not a set")
  isEmpty = SmtBinary Eq setExpr emptySet
  generateVars n | n > 0 =
    map (\n -> SmtVariable ("v" ++ (show n)) elementSort False []) [1 .. n]
  generateVars n | n <= 0 = error ((show n) ++ " must be positive")
  generateSet []       = error "expects at least one variable"
  generateSet (x : []) = SmtUnary Singleton (SmtVar x)
  generateSet (x : xs) =
    SmtBinary Union (SmtUnary Singleton (SmtVar x)) (generateSet xs)

translateArithmetic :: (Env, AlloyExpr) -> (Env, SmtExpr)
translateArithmetic (env, (AlloyBinary op x y)) =
  error (show (AlloyBinary op x y))

translateIntConstant :: Env -> Int -> (Env, SmtExpr)
translateIntConstant env n = (env3, smtExpr)
 where
  env3 = if containsDeclaration env varName
    then env
    else env2
      where 
        env1 = addDeclaration env (SmtVariable varName uninterpretedUInt False [])
        env2 = addAssertion env1 assertion
        assertion = Assertion (show n) (SmtBinary Eq callExpr (SmtIntConstant n))
        callExpr = SmtCall intValue [smtExpr]
  varName = "u." ++ (show n)  
  smtExpr = SmtVar (getDeclaration env3 varName)
