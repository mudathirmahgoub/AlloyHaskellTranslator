{-# LANGUAGE RecordWildCards #-}
module Translator where
import           AlloyOperators
import           SmtOperators
import           Alloy
import           Smt
import           Env

translateModel :: AlloyModel -> SmtScript
translateModel model = smtScript6
 where
  sigs       = signatures model
  smtScript1 = declareSignatures emptySmtScript sigs
  smtScript2 = translateSignatures smtScript1 sigs
  smtScript3 = translateSignatureFacts smtScript2 sigs
  smtScript4 = translateFacts smtScript3 (facts model)
  -- axioms for none, univAtom, univInt, intValue
  smtScript5 = addSpecialAssertions smtScript4
  smtScript6 = translateCommands smtScript5 (commands model)

translateSignatures :: SmtScript -> [Sig] -> SmtScript
translateSignatures smtScript [] = smtScript
translateSignatures smtScript xs =
  translateHierarchy smtScript (filter isTopLevel xs)

declareSignatures :: SmtScript -> [Sig] -> SmtScript
declareSignatures smtScript xs = foldl declareSignature smtScript xs

declareSignature :: SmtScript -> Sig -> SmtScript
declareSignature smtScript Univ   = addConstant smtScript univAtom
declareSignature smtScript SigInt = addConstant smtScript univInt
declareSignature smtScript None   = addConstant smtScript none
declareSignature _ SigString =
  error ("Strings are not supported yet in alloy.")
declareSignature smtScript sig = addConstant
  smtScript
  SmtVariable { name = label sig, sort = s, isOriginal = True }
  where s = translateType (Prod [sig])

translateHierarchy :: SmtScript -> [Sig] -> SmtScript
translateHierarchy smtScript xs = foldl translateSignature smtScript xs

translateSignature :: SmtScript -> Sig -> SmtScript
translateSignature smtScript Univ   = smtScript
translateSignature smtScript SigInt = smtScript
translateSignature smtScript None   = smtScript
translateSignature _ SigString =
  error ("Strings are not supported yet in alloy.")
translateSignature smtScript PrimSig {..} = smtScript5
 where
  smtScript0 = foldl translateSignature smtScript children
  smtScript1 = translateSigMultiplicity smtScript0 PrimSig { .. }
  smtScript2 = translateParent smtScript1 PrimSig { .. }
  smtScript3 = translateDisjointChildren smtScript2 PrimSig { .. }
  smtScript4 = translateAbstract smtScript3 PrimSig { .. }
  smtScript5 = translateFields smtScript4 PrimSig { .. }

translateSignature smtScript SubsetSig {..} = smtScript3
 where
  smtScript1 = translateSigMultiplicity smtScript SubsetSig { .. }
  smtScript2 = translateParent smtScript1 SubsetSig { .. }
  smtScript3 = translateFields smtScript2 SubsetSig { .. }

-- require sig is already defined in SMTScript p
translateSigMultiplicity :: SmtScript -> Sig -> SmtScript
-- sig a
-- use different from empty set
translateSigMultiplicity smtScript sig = addAssertion smtScript assertion
 where
  c = getConstant smtScript (label sig)
  s = case translateType (Prod [sig]) of
    Set (Tuple [Atom]) -> Atom
    Set (Tuple [UInt]) -> UInt
    _                  -> error ("invalid sig sort " ++ (show s))
  x           = SmtVariable { name = "x", sort = s, isOriginal = False }
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
translateParent :: SmtScript -> Sig -> SmtScript
translateParent smtScript PrimSig {..} = addAssertion smtScript assertion
 where
  childVar  = getConstant smtScript primLabel
  parentVar = getConstant smtScript (label parent)
  subset    = SmtBinary Subset (SmtVar childVar) (SmtVar parentVar)
  assertion = Assertion ("parent " ++ primLabel) subset

translateParent smtScript SubsetSig {..} = addAssertion smtScript assertion
 where
  childVar   = getConstant smtScript subsetLabel
  parentVars = map (getConstant smtScript . label) parents
  function parentVar = SmtBinary Subset (SmtVar childVar) (SmtVar parentVar)
  subsets   = SmtMultiArity And (map function parentVars)
  assertion = Assertion ("parents " ++ subsetLabel) subsets

translateParent _ _ = undefined


translateDisjointChildren :: SmtScript -> Sig -> SmtScript
translateDisjointChildren smtScript PrimSig {..} = addAssertion smtScript
                                                                assertion
 where
  function (x, y) = SmtBinary
    Eq
    empty
    (SmtBinary Intersection (SmtVar xVar) (SmtVar yVar))
   where
    xVar = getConstant smtScript (label x)
    yVar = getConstant smtScript (label y)
  disjointChildren zs = map function zs
  sigSort   = translateType (Prod [PrimSig { .. }])
  empty     = SmtUnary EmptySet (SortExpr sigSort)
  pairs     = [ (u, v) | u <- children, v <- children, (label u) < (label v) ]
  andExpr   = SmtMultiArity And (disjointChildren pairs)
  assertion = Assertion ("disjoint children of " ++ primLabel) andExpr
translateDisjointChildren _ sig =
  error ((label sig) ++ " is not a prime signature")

translateAbstract :: SmtScript -> Sig -> SmtScript
translateAbstract smtScript PrimSig {..} =
  case isAbstract && not (null children) of
    False -> smtScript
    True  -> addAssertion smtScript assertion
     where
      function x y = SmtBinary Union x y
      sigVar    = getConstant smtScript primLabel
      union     = foldl function empty variables
      variables = map (SmtVar . getConstant smtScript . label) children
      sigSort   = translateType (Prod [PrimSig { .. }])
      empty     = SmtUnary EmptySet (SortExpr (sort sigVar))
      equal     = SmtBinary Eq (SmtVar sigVar) union
      assertion = Assertion ("abstract " ++ primLabel) equal
translateAbstract _ sig = error ((label sig) ++ " is not a prime signature")

translateFields :: SmtScript -> Sig -> SmtScript
translateFields smtScript sig = smtScript4
 where
  groups        = fields sig
  individuals   = splitDecls groups
  smtScript1    = foldl (declareField sig) smtScript individuals
  smtScript2    = foldl (translateField sig) smtScript1 individuals
  disjointExprs = translateDisjointDecls smtScript2 emptyEnv groups
  smtScript3    = addAssertion
    smtScript2
    (Assertion ("disjoint " ++ (show groups)) disjointExprs)
  smtScript4 = translateDisjoint2Decls smtScript3 individuals

declareField :: Sig -> SmtScript -> Decl -> SmtScript
declareField sig smtScript Decl {..} = addConstant smtScript constant
 where
  constant = SmtVariable { name       = concat (declNames Decl { .. })
                         , sort       = smtSort
                         , isOriginal = True
                         }
  smtSort = translateType (alloyType (AlloyBinary ARROW (Signature sig) expr))

translateField :: Sig -> SmtScript -> Decl -> SmtScript
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


translateField sig smtScript Decl {..} = smtScript1 -- ToDo: fix this
 where
  fieldVar      = getConstant smtScript (concat (declNames Decl { .. }))
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
    where (_, smtExpr) = translate (smtScript, emptyEnv, allExpr)
  multiplicityAssertion =
    Assertion ((show fieldVar) ++ " field multiplicity") smtMultiplicity
  noMuliplicity = removeMultiplicity expr
  substitution  = substitute this (Signature sig) noMuliplicity
  productExpr   = AlloyBinary ARROW (Signature sig) substitution
  subsetExpr    = AlloyBinary IN (Field Decl { .. }) productExpr
  subsetAssertion =
    translateFormula smtScript ((show fieldVar) ++ " field subset") subsetExpr
  smtScript1 = addAssertions smtScript [multiplicityAssertion, subsetAssertion]

translateDisjointDecls :: SmtScript -> Env -> [Decl] -> SmtExpr
translateDisjointDecls smtScript env decls =
  SmtMultiArity And (map (translateDisjointDecl smtScript env) decls)

translateDisjointDecl :: SmtScript -> Env -> Decl -> SmtExpr
translateDisjointDecl smtScript env decl = andExpr
 where
  function (x, y) = SmtBinary
    Eq
    empty
    (SmtBinary Intersection (SmtVar xVar) (SmtVar yVar))
   where
    xVar  = getVariable (smtScript, env) (alloyVarName x)
    yVar  = getVariable (smtScript, env) (alloyVarName y)
    empty = SmtUnary EmptySet (SortExpr (sort xVar))
  pairs =
    [ (u, v)
    | u <- names decl
    , v <- names decl
    , (alloyVarName u) < (alloyVarName v)
    ]
  andExpr = SmtMultiArity And (map function pairs)


translateDisjoint2Decls :: SmtScript -> [Decl] -> SmtScript
translateDisjoint2Decls smtScript _ = smtScript -- ToDo: fix this

translateSignatureFacts :: SmtScript -> [Sig] -> SmtScript
translateSignatureFacts smtScript [] = smtScript
translateSignatureFacts smtScript xs =
  foldl translateSignatureFact smtScript xs

-- sig s{...}{expr} is translated into
-- {all this: s | expr}
translateSignatureFact :: SmtScript -> Sig -> SmtScript
translateSignatureFact smtScript sig = case (sigfacts sig) of
  [] -> smtScript
  _  -> smtScript1   where
    sigVar       = getConstant smtScript (label sig)
    smtScript1   = addAssertion smtScript assertion
    assertion    = Assertion ((show sigVar) ++ " sig facts") smtExpr
    (_, smtExpr) = translate (smtScript, emptyEnv, allExpr)
    allExpr      = AlloyQt All [decl] andExpr
    andExpr      = AlloyList ListAND (sigfacts sig)
    this         = AlloyVariable "this" (Prod [sig])
    decl         = Decl { names     = [this]
                        , expr      = AlloyUnary ONEOF (Signature sig)
                        , disjoint  = False
                        , disjoint2 = False
                        }

translateFacts :: SmtScript -> [Fact] -> SmtScript
translateFacts smtScript xs = foldl translateFact smtScript xs

translateFact :: SmtScript -> Fact -> SmtScript
translateFact smtScript (Fact name alloyExpr) = addAssertion smtScript
                                                             assertion
 where
  assertion    = Assertion name smtExpr
  (_, smtExpr) = translate (smtScript, emptyEnv, alloyExpr)

addSpecialAssertions :: SmtScript -> SmtScript
addSpecialAssertions smtScript = smtScript -- ToDo: change this later

translateCommands :: SmtScript -> [Command] -> SmtScript
translateCommands smtScript xs = foldl translateCommand smtScript xs

translateCommand :: SmtScript -> Command -> SmtScript
translateCommand _ _ = undefined

translateFormula :: SmtScript -> String -> AlloyExpr -> Assertion
translateFormula smtScript string alloyExpr = assertion
 where
  (env, smtExpr) = translate (smtScript, emptyEnv, alloyExpr)
  formula        = translateAuxiliaryFormula env smtExpr
  assertion      = Assertion string formula

translateAuxiliaryFormula :: Env -> SmtExpr -> SmtExpr
translateAuxiliaryFormula Env { auxiliaryFormula = Nothing } expr = expr
translateAuxiliaryFormula Env { auxiliaryFormula = (Just aux) } expr =
  case aux of
    SmtQt Exists variables body ->
      SmtQt Exists variables (SmtMultiArity And [body, expr])
    SmtQt ForAll variables body ->
      SmtQt ForAll variables (SmtBinary Implies body expr)
    _ -> error ("Auxiliary formula " ++ (show aux) ++ " is not supported")

translate :: (SmtScript, Env, AlloyExpr) -> (Env, SmtExpr)
translate (smtScript, env, Signature x) =
  (env, SmtVar (getConstant smtScript (label x)))
translate (smtScript, env, Field Decl {..}) =
  (env, SmtVar (getConstant smtScript (getFieldName Decl { .. })))
translate (_, _, (AlloyConstant c sig)) = case sig of
  SigInt -> undefined
  _      -> error ("Constant " ++ (show c) ++ " is not supported")
translate (smtScript, env, AlloyVar x) = (env, SmtVar variable)
  where variable = getVariable (smtScript, env) (alloyVarName x)
translate (_, _, (AlloyUnary SOMEOF _)) = undefined
translate (_, _, (AlloyUnary LONEOF _)) = undefined
translate (smtScript, env, (AlloyUnary ONEOF x)) =
  translate (smtScript, env, x)
translate (_, _, (AlloyUnary SETOF _)    ) = undefined
translate (_, _, (AlloyUnary EXACTLYOF _)) = undefined
translate (smtScript, env, (AlloyUnary NOT x)) =
  (env, SmtUnary Not (second (translate (smtScript, env, x))))
translate (_        , _  , (AlloyUnary NO _)) = undefined
translate (smtScript, env, AlloyUnary SOME x) = (env, someExpr)
 where
  someExpr        = translateAuxiliaryFormula env1 notEmpty
  (env1, setExpr) = translate (smtScript, env, x)
  empty           = SmtUnary EmptySet (SortExpr (smtType setExpr))
  equal           = SmtBinary Eq empty setExpr
  notEmpty        = SmtUnary Not equal

translate (_, _, (AlloyUnary LONE _)     ) = undefined
translate (_, _, (AlloyUnary ONE _)      ) = undefined
translate (_, _, (AlloyUnary TRANSPOSE _)) = undefined
translate (_, _, (AlloyUnary RCLOSURE _) ) = undefined
translate (_, _, (AlloyUnary CLOSURE _)  ) = undefined
translate (_, _, (AlloyUnary CARDINALITY _)) =
  error ("Cardinality not supported here.")
translate (_, _, AlloyUnary CAST2INT _) = undefined
translate (_, _, AlloyUnary CAST2SIGINT _) = undefined
translate (smtScript, env, (AlloyUnary NOOP x)) = translate (smtScript, env, x)
-- binary expressions
translate (smtScript, env, (AlloyBinary ARROW x y)) =
  (env, SmtBinary Product a b)
 where
  (_, a) = translate (smtScript, env, x)
  (_, b) = translate (smtScript, env, y)

translate (_, _, (AlloyBinary ANY_ARROW_SOME _ _)  ) = undefined
translate (_, _, (AlloyBinary ANY_ARROW_ONE _ _)   ) = undefined
translate (_, _, (AlloyBinary ANY_ARROW_LONE _ _)  ) = undefined
translate (_, _, (AlloyBinary SOME_ARROW_ANY _ _)  ) = undefined
translate (_, _, (AlloyBinary SOME_ARROW_SOME _ _) ) = undefined
translate (_, _, (AlloyBinary SOME_ARROW_ONE _ _)  ) = undefined
translate (_, _, (AlloyBinary SOME_ARROW_LONE _ _) ) = undefined
translate (_, _, (AlloyBinary ONE_ARROW_ANY _ _)   ) = undefined
translate (_, _, (AlloyBinary ONE_ARROW_SOME _ _)  ) = undefined
translate (_, _, (AlloyBinary ONE_ARROW_ONE _ _)   ) = undefined
translate (_, _, (AlloyBinary ONE_ARROW_LONE _ _)  ) = undefined
translate (_, _, (AlloyBinary LONE_ARROW_ANY _ _)  ) = undefined
translate (_, _, (AlloyBinary LONE_ARROW_SOME _ _) ) = undefined
translate (_, _, (AlloyBinary LONE_ARROW_ONE _ _)  ) = undefined
translate (_, _, (AlloyBinary LONE_ARROW_LONE _ _) ) = undefined
translate (_, _, (AlloyBinary ISSEQ_ARROW_LONE _ _)) = undefined
translate (smtScript, env, (AlloyBinary JOIN x y)) =
  (env, SmtBinary Join smtX smtY)
 where
  smtX = makeRelation (second (translate (smtScript, env, x)))
  smtY = makeRelation (second (translate (smtScript, env, y)))
translate (_, _, (AlloyBinary DOMAIN _ _)) = undefined
translate (_, _, (AlloyBinary RANGE _ _) ) = undefined
translate (smtScript, env, (AlloyBinary INTERSECT x y)) =
  ( env
  , SmtBinary Intersection
              (second (translate (smtScript, env, x)))
              (second (translate (smtScript, env, y)))
  )
translate (_, _, (AlloyBinary PLUSPLUS _ _)) = undefined
translate (smtScript, env, (AlloyBinary PLUS x y)) =
  ( env
  , SmtBinary Union
              (second (translate (smtScript, env, x)))
              (second (translate (smtScript, env, y)))
  )
translate (_, _, (AlloyBinary IPLUS _ _) ) = undefined
translate (_, _, (AlloyBinary MINUS _ _) ) = undefined
translate (_, _, (AlloyBinary IMINUS _ _)) = undefined
translate (_, _, (AlloyBinary MUL _ _)   ) = undefined
translate (_, _, (AlloyBinary DIV _ _)   ) = undefined
translate (_, _, (AlloyBinary REM _ _)   ) = undefined
translate (smtScript, env, (AlloyBinary IMPLIES x y)) =
  ( env
  , SmtBinary Implies
              (second (translate (smtScript, env, x)))
              (second (translate (smtScript, env, y)))
  )

translate (smtScript, env, (AlloyBinary Less x y)) =
  (env, translateComparison (smtScript, env, (AlloyBinary Less x y)))
translate (smtScript, env, (AlloyBinary LTE x y)) =
  (env, translateComparison (smtScript, env, (AlloyBinary LTE x y)))
translate (smtScript, env, (AlloyBinary Greater x y)) =
  (env, translateComparison (smtScript, env, (AlloyBinary Greater x y)))
translate (smtScript, env, (AlloyBinary GTE x y)) =
  (env, translateComparison (smtScript, env, (AlloyBinary GTE x y)))
translate (smtScript, env, (AlloyBinary NOT_LT x y)) =
  (env, translateComparison (smtScript, env, (AlloyBinary NOT_LT x y)))
translate (smtScript, env, (AlloyBinary NOT_LTE x y)) =
  (env, translateComparison (smtScript, env, (AlloyBinary NOT_LTE x y)))
translate (smtScript, env, (AlloyBinary NOT_GT x y)) =
  (env, translateComparison (smtScript, env, (AlloyBinary NOT_GT x y)))
translate (smtScript, env, (AlloyBinary NOT_GTE x y)) =
  (env, translateComparison (smtScript, env, (AlloyBinary NOT_GTE x y)))
translate (smtScript, env, (AlloyBinary EQUALS x y)) =
  (env, translateComparison (smtScript, env, (AlloyBinary EQUALS x y)))
translate (smtScript, env, (AlloyBinary NOT_EQUALS x y)) =
  (env, translateComparison (smtScript, env, (AlloyBinary NOT_EQUALS x y)))

translate (_        , _  , (AlloyBinary SHL _ _)) = undefined
translate (_        , _  , (AlloyBinary SHA _ _)) = undefined
translate (_        , _  , (AlloyBinary SHR _ _)) = undefined

-- Translation of 'x in y' where A = translate x, B = translate Y
-- left sort | right sort | Translation
-- -------------------------------------
-- tuple     | tuple      | (= A B)
-- tuple     | set        | (member tuple set)
-- set       | set        | (subset A B)
translate (smtScript, env, (AlloyBinary IN x y) ) = (env, auxiliaryB)
 where
  smtIn     = memberOrSubset a b (smtType a) (smtType b)
  (envA, a) = translate (smtScript, env, x)
  (envB, b) = translate (smtScript, env, y)
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

translate (smtScript, env, (AlloyBinary NOT_IN x y)) = (env, SmtUnary Not expr)
  where (_, expr) = translate (smtScript, env, AlloyBinary IN x y)
translate (smtScript, env, (AlloyBinary AND x y)) =
  ( env
  , SmtMultiArity
    And
    [ (second (translate (smtScript, env, x)))
    , (second (translate (smtScript, env, y)))
    ]
  )
translate (smtScript, env, (AlloyBinary OR x y)) =
  ( env
  , SmtMultiArity
    Or
    [ (second (translate (smtScript, env, x)))
    , (second (translate (smtScript, env, y)))
    ]
  )
translate (smtScript, env, (AlloyBinary IFF x y)) =
  ( env
  , SmtBinary Eq
              (second (translate (smtScript, env, x)))
              (second (translate (smtScript, env, y)))
  )
-- if then else expression
translate (smtScript, env, (AlloyITE c x y)) =
  ( env
  , SmtIte (second (translate (smtScript, env, c)))
           (second (translate (smtScript, env, x)))
           (second (translate (smtScript, env, y)))
  )
-- quantified expression
-- all x: some A| all y: one x | some y
-- check with Andy with quantifiers versus nested quantifiers
translate (smtScript, env, (AlloyQt op decls body)) = (env2, smtQt)
 where
  variableTuples   = map (translateDecl smtScript env) (splitDecls decls)
  variables        = map first variableTuples
  rangeConstraints = concat (map second variableTuples)
  env1             = addVariables env variables
  disjoint         = translateDisjointDecls smtScript env1 decls
  constraints      = SmtMultiArity And (disjoint : rangeConstraints)
  (env2, bodyExpr) = translate (smtScript, env1, body)
  smtQt            = translateQt op
   where
    translateQt All = case auxiliaryFormula env2 of
      Nothing ->
        SmtQt ForAll variables (SmtBinary Implies constraints bodyExpr)
      Just (SmtQt Exists existsVars existsBody) -> SmtQt
        ForAll
        variables
        (SmtBinary Implies constraints newBody)
       where
        newBody =
          (SmtQt Exists existsVars (SmtMultiArity And [existsBody, bodyExpr]))
  translateQt No            = SmtUnary Not (translateQt All)
  translateQt Lone          = undefined
  translateQt Some          = undefined
  translateQt Sum           = undefined
  translateQt Comprehension = undefined


-- let expression
translate (smtScript, env, (AlloyLet var alloyExpr body)) = (env3, smtLet)
 where
  smtVar          = SmtVariable (alloyVarName var) (smtType smtExpr) True
  (env1, smtExpr) = translate (smtScript, env, alloyExpr)
  env2            = addVariable env1 smtVar
  (env3, smtBody) = translate (smtScript, env2, body)
  smtLet          = SmtLet [(smtVar, smtExpr)] smtBody

translate (smtScript, env, AlloyList op xs) = case op of
  ListAND -> (env, SmtMultiArity And exprs)
    where exprs = map second (map (\x -> translate (smtScript, env, x)) xs)
  ListOR     -> undefined
  TOTALORDER -> undefined
  DISJOINT   -> undefined


-- types
translateType :: AlloyType -> Sort
translateType (Prod xs) = Set (Tuple ys)
  where ys = map (\x -> if isInt (Signature x) then UInt else Atom) xs
translateType AlloyBool = SmtBool



-- SmtExpr for multiplicity and range constraints
-- ToDo: optimize this such that this is called once for Decl like (x, y : expr)    
translateDecl :: SmtScript -> Env -> Decl -> (SmtVariable, [SmtExpr])
translateDecl smtScript env decl = (var, exprs)
 where
  varName      = concat (declNames decl)
  (var, exprs) = translateDeclExpr (smtScript, env, expr decl)
  translateDeclExpr (smtScript, env, AlloyUnary ONEOF x) = (variable, [member])
   where
    (_, smtExpr) = translate (smtScript, env, x)
    varSort      = case (smtType smtExpr) of
      Set (Tuple (x : [])) -> Tuple (x : []) -- arity 1
      s -> error ("Expected a relation with arity 1. Found " ++ (show s))
    variable =
      SmtVariable { name = varName, sort = varSort, isOriginal = True }
    member = SmtBinary Member (SmtVar variable) smtExpr

  translateDeclExpr (smtScript, env, AlloyUnary SOMEOF x) =
    (variable, [subset, notEmpty])
   where
    (_, smtExpr) = translate (smtScript, env, x)
    varSort      = smtType smtExpr
    variable =
      SmtVariable { name = varName, sort = varSort, isOriginal = True }
    subset   = SmtBinary Subset (SmtVar variable) smtExpr
    emptySet = SmtUnary EmptySet (SortExpr varSort)
    notEmpty = SmtUnary Not (SmtBinary Eq (SmtVar variable) emptySet)
  translateDeclExpr (smtScript, env, AlloyUnary LONEOF x) =
    (variable, [subset, loneExpr])
   where
    (_, smtExpr) = translate (smtScript, env, x)
    varSort      = smtType smtExpr
    variable =
      SmtVariable { name = varName, sort = varSort, isOriginal = True }
    subset      = SmtBinary Subset (SmtVar variable) smtExpr
    emptySet    = SmtUnary EmptySet (SortExpr varSort)
    empty       = SmtBinary Eq (SmtVar variable) emptySet
    elementSort = getElementSort varSort
    element     = SmtVariable { name       = varName ++ "Singleton"
                              , sort       = elementSort
                              , isOriginal = False
                              }
    singleton   = (SmtUnary Singleton (SmtMultiArity MkTuple [SmtVar element]))
    isSingleton = SmtBinary Eq (SmtVar variable) singleton
    existsExpr  = SmtQt Exists [element] subset
    loneExpr    = SmtMultiArity Or [empty, existsExpr]

  translateDeclExpr (smtScript, env, AlloyUnary SETOF x) = (variable, [subset])
   where
    (_, smtExpr) = translate (smtScript, env, x)
    varSort      = smtType smtExpr
    variable =
      SmtVariable { name = varName, sort = varSort, isOriginal = True }
    subset = SmtBinary Subset (SmtVar variable) smtExpr

  translateDeclExpr (smtScript, env, AlloyBinary _ _ _) = undefined
  translateDeclExpr (_, _, x) = error ("Invalid decl expr: " ++ (show x))

translateComparison :: (SmtScript, Env, AlloyExpr) -> SmtExpr

translateComparison (smtScript, env, (AlloyBinary op (AlloyUnary CARDINALITY x) (AlloyConstant c SigInt)))
  = translateAuxiliaryFormula env1 smtExpr
 where
  (env1, setExpr) = translate (smtScript, env, x)
  n               = read c
  smtExpr         = translateCardinalityComparison env op setExpr n

translateComparison (smtScript, env, (AlloyBinary op (AlloyConstant c SigInt) (AlloyUnary CARDINALITY x)))
  = case op of
    Less -> translateComparison
      ( smtScript
      , env
      , (AlloyBinary Greater (AlloyUnary CARDINALITY x) (AlloyConstant c SigInt)
        )
      )
    LTE -> translateComparison
      ( smtScript
      , env
      , (AlloyBinary GTE (AlloyUnary CARDINALITY x) (AlloyConstant c SigInt))
      )
    Greater -> translateComparison
      ( smtScript
      , env
      , (AlloyBinary Less (AlloyUnary CARDINALITY x) (AlloyConstant c SigInt))
      )
    GTE -> translateComparison
      ( smtScript
      , env
      , (AlloyBinary LTE (AlloyUnary CARDINALITY x) (AlloyConstant c SigInt))
      )
    NOT_LT -> translateComparison
      ( smtScript
      , env
      , (AlloyBinary NOT_GT (AlloyUnary CARDINALITY x) (AlloyConstant c SigInt))
      )
    NOT_LTE -> translateComparison
      ( smtScript
      , env
      , (AlloyBinary NOT_GTE (AlloyUnary CARDINALITY x) (AlloyConstant c SigInt)
        )
      )
    NOT_GT -> translateComparison
      ( smtScript
      , env
      , (AlloyBinary NOT_LT (AlloyUnary CARDINALITY x) (AlloyConstant c SigInt))
      )
    NOT_GTE -> translateComparison
      ( smtScript
      , env
      , (AlloyBinary NOT_LTE (AlloyUnary CARDINALITY x) (AlloyConstant c SigInt)
        )
      )
    EQUALS -> translateComparison
      ( smtScript
      , env
      , (AlloyBinary EQUALS (AlloyUnary CARDINALITY x) (AlloyConstant c SigInt))
      )
    NOT_EQUALS -> translateComparison
      ( smtScript
      , env
      , (AlloyBinary NOT_EQUALS
                     (AlloyUnary CARDINALITY x)
                     (AlloyConstant c SigInt)
        )
      )
    _ -> error "Invalid comparision operator"

-- general case for = , !=
translateComparison (smtScript, env, (AlloyBinary EQUALS x y)) = smtExpr
 where
  (env1, xExpr) = (translate (smtScript, env, x))
  (env2, yExpr) = (translate (smtScript, env1, y))
  equal         = SmtBinary Eq xExpr yExpr
  smtExpr       = translateAuxiliaryFormula env2 equal
translateComparison (smtScript, env, (AlloyBinary NOT_EQUALS x y)) = smtExpr
 where
  smtExpr = SmtUnary Not equal
  equal   = translateComparison (smtScript, env, (AlloyBinary EQUALS x y))


-- arithmetic
translateComparison (smtScript, env, (AlloyBinary op x y)) =
  translateArithmetic (smtScript, env, (AlloyBinary op x y))


translateCardinalityComparison
  :: Env -> AlloyBinaryOp -> SmtExpr -> Int -> SmtExpr
translateCardinalityComparison (Env aux vars index) op setExpr n = case op of
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
  NOT_LT -> translateCardinalityComparison (Env aux vars index) GTE setExpr n
  NOT_LTE ->
    translateCardinalityComparison (Env aux vars index) Greater setExpr n
  NOT_GT  -> translateCardinalityComparison (Env aux vars index) LTE setExpr n
  NOT_GTE -> translateCardinalityComparison (Env aux vars index) Less setExpr n
  EQUALS  -> case n of
    n | n <= -1   -> SmtBoolConstant False
    n | n == 0    -> isEmpty
    n | otherwise -> SmtQt Exists vars (SmtBinary Eq setExpr cardinalitySet)
     where
      vars           = generateVars (n - 1)
      cardinalitySet = generateSet vars
  NOT_EQUALS -> SmtUnary
    Not
    (translateCardinalityComparison (Env aux vars index) EQUALS setExpr n)
  _ -> error "Invalid comparision operator"
 where
  setSort     = (smtType setExpr)
  emptySet    = SmtUnary EmptySet (SortExpr setSort)
  elementSort = case setSort of
    Set x -> x
    _     -> error ((show setSort) ++ " is not a set")
  isEmpty = SmtBinary Eq setExpr emptySet
  generateVars n | n > 0 =
    map (\n -> SmtVariable ("v" ++ (show n)) elementSort False) [1 .. n]
  generateVars n | n <= 0 = error ((show n) ++ " must be positive")
  generateSet []       = error "expects at least one variable"
  generateSet (x : []) = SmtUnary Singleton (SmtVar x)
  generateSet (x : xs) =
    SmtBinary Union (SmtUnary Singleton (SmtVar x)) (generateSet xs)

translateArithmetic :: (SmtScript, Env, AlloyExpr) -> SmtExpr
translateArithmetic (smtScript, env, (AlloyBinary op x y)) =
  error (show (AlloyBinary op x y))
