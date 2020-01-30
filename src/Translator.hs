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
declareSignature smtScript Univ      = addConstant smtScript univAtom
declareSignature smtScript SigInt    = addConstant smtScript univInt
declareSignature smtScript None      = addConstant smtScript none
declareSignature _         SigString = undefined
declareSignature smtScript sig       = addConstant
  smtScript
  SmtVariable { name = label sig, sort = s, isOriginal = True }
  where s = translateType (Prod [sig])

translateHierarchy :: SmtScript -> [Sig] -> SmtScript
translateHierarchy smtScript xs = foldl translateSignature smtScript xs

translateSignature :: SmtScript -> Sig -> SmtScript
translateSignature smtScript Univ         = smtScript
translateSignature smtScript SigInt       = smtScript
translateSignature smtScript None         = smtScript
translateSignature _         SigString    = undefined
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
  c           = getConstant smtScript (label sig)
  s           = translateType (Prod [sig])
  x           = SmtVariable { name = "x", sort = s, isOriginal = False }
  singleton   = (SmtUnary Singleton (SmtMultiArity MkTuple [SmtVar x]))
  isSingleton = SmtBinary Eq (SmtVar c) singleton
  subset      = SmtBinary Subset (SmtVar c) singleton
  empty       = SmtUnary EmptySet (SortExpr (Set (Tuple [s])))
  existsOne   = SmtQt Exists [x] isSingleton
  existsSome  = SmtQt Exists [x] subset
  orExpr      = SmtMultiArity Or [existsOne, empty]
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
  empty     = SmtUnary EmptySet (SortExpr (Set (Tuple [sigSort])))
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
      empty     = SmtUnary EmptySet (SortExpr (Set (Tuple [sigSort])))
      equal     = SmtBinary Eq (SmtVar sigVar) union
      assertion = Assertion ("Abstract " ++ primLabel) equal
translateAbstract _ sig = error ((label sig) ++ " is not a prime signature")

translateFields :: SmtScript -> Sig -> SmtScript
translateFields smtScript sig = smtScript4
 where
  groups      = fields sig
  individuals = splitDecls groups
  smtScript1  = foldl (declareField sig) smtScript individuals
  smtScript2  = foldl (translateField sig) smtScript1 individuals
  smtScript3  = translateDisjointFields smtScript2 groups
  smtScript4  = translateDisjoint2Fields smtScript3 individuals

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
  decl          = Decl { names     = [s]
                       , expr      = Signature sig
                       , disjoint  = False
                       , disjoint2 = False
                       }
  allExpr         = AlloyQt All [decl] alloyLet
  smtMultiplicity = smtExpr
    where (_, smtExpr) = translate (smtScript, emptyEnv, allExpr)
  multiplicityAssertion =
    Assertion ((show fieldVar) ++ " multiplicity") smtMultiplicity
  noMuliplicity = removeMultiplicity expr
  substitution  = substitute this (Signature sig) noMuliplicity
  productExpr   = AlloyBinary ARROW (Signature sig) substitution
  subsetExpr    = AlloyBinary IN (Field Decl { .. }) productExpr
  subsetAssertion =
    translateFormula smtScript ((show fieldVar) ++ " subset") subsetExpr
  smtScript1 = addAssertions smtScript [multiplicityAssertion, subsetAssertion]

translateDisjointFields :: SmtScript -> [Decl] -> SmtScript
translateDisjointFields smtScript _ = smtScript -- ToDo: fix this

translateDisjoint2Fields :: SmtScript -> [Decl] -> SmtScript
translateDisjoint2Fields smtScript _ = smtScript -- ToDo: fix this

translateSignatureFacts :: SmtScript -> [Sig] -> SmtScript
translateSignatureFacts smtScript [] = smtScript
translateSignatureFacts smtScript xs =
  foldl translateSignatureFact smtScript xs

translateSignatureFact :: SmtScript -> Sig -> SmtScript
translateSignatureFact smtScript sig = case (sigfacts sig) of
  [] -> smtScript
  _  -> undefined

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
  (env, SmtVar (getConstant smtScript (getFieldName Decl{..})))
translate (_, _, (AlloyConstant c sig)) = case sig of
  SigInt -> undefined
  _      -> error ("Constant " ++ (show c) ++ " is not supported")
translate (_, _, AlloyVar _              ) = undefined
translate (_, _, (AlloyUnary SOMEOF _)   ) = undefined
translate (_, _, (AlloyUnary LONEOF _)   ) = undefined
translate (_, _, (AlloyUnary ONEOF _)    ) = undefined
translate (_, _, (AlloyUnary SETOF _)    ) = undefined
translate (_, _, (AlloyUnary EXACTLYOF _)) = undefined
translate (p, env, (AlloyUnary NOT x)) =
  (env, SmtUnary Not (second (translate (p, env, x))))
translate (_, _  , (AlloyUnary NO _)         ) = undefined
translate (_, _  , (AlloyUnary SOME _)       ) = undefined
translate (_, _  , (AlloyUnary LONE _)       ) = undefined
translate (_, _  , (AlloyUnary ONE _)        ) = undefined
translate (_, _  , (AlloyUnary TRANSPOSE _)  ) = undefined
translate (_, _  , (AlloyUnary RCLOSURE _)   ) = undefined
translate (_, _  , (AlloyUnary CLOSURE _)    ) = undefined
translate (_, _  , (AlloyUnary CARDINALITY _)) = undefined
translate (_, _  , AlloyUnary CAST2INT _     ) = undefined
translate (_, _  , AlloyUnary CAST2SIGINT _  ) = undefined
translate (p, env, (AlloyUnary NOOP x)       ) = translate (p, env, x)
-- binary expressions
translate (p, env, (AlloyBinary ARROW x y)   ) = (env, SmtBinary Product a b)
 where
  (_, a) = translate (p, env, x)
  (_, b) = translate (p, env, y)

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
translate (p, env, (AlloyBinary JOIN x y)) =
  ( env
  , SmtBinary Join
              (second (translate (p, env, x)))
              (second (translate (p, env, y)))
  )
translate (_, _, (AlloyBinary DOMAIN _ _)) = undefined
translate (_, _, (AlloyBinary RANGE _ _) ) = undefined
translate (p, env, (AlloyBinary INTERSECT x y)) =
  ( env
  , SmtBinary Intersection
              (second (translate (p, env, x)))
              (second (translate (p, env, y)))
  )
translate (_, _, (AlloyBinary PLUSPLUS _ _)) = undefined
translate (p, env, (AlloyBinary PLUS x y)) =
  ( env
  , SmtBinary Union
              (second (translate (p, env, x)))
              (second (translate (p, env, y)))
  )
translate (_, _, (AlloyBinary IPLUS _ _) ) = undefined
translate (_, _, (AlloyBinary MINUS _ _) ) = undefined
translate (_, _, (AlloyBinary IMINUS _ _)) = undefined
translate (_, _, (AlloyBinary MUL _ _)   ) = undefined
translate (_, _, (AlloyBinary DIV _ _)   ) = undefined
translate (_, _, (AlloyBinary REM _ _)   ) = undefined
translate (p, env, (AlloyBinary EQUALS x y)) =
  ( env
  , SmtBinary Eq
              (second (translate (p, env, x)))
              (second (translate (p, env, y)))
  )
translate (p, env, (AlloyBinary NOT_EQUALS x y)) =
  ( env
  , SmtUnary
    Not
    (SmtBinary Eq
               (second (translate (p, env, x)))
               (second (translate (p, env, y)))
    )
  )
translate (p, env, (AlloyBinary IMPLIES x y)) =
  ( env
  , SmtBinary Implies
              (second (translate (p, env, x)))
              (second (translate (p, env, y)))
  )
translate (p, env, (AlloyBinary Less x y)) =
  ( env
  , SmtBinary Lt
              (second (translate (p, env, x)))
              (second (translate (p, env, y)))
  )
translate (p, env, (AlloyBinary LTE x y)) =
  ( env
  , SmtBinary Lte
              (second (translate (p, env, x)))
              (second (translate (p, env, y)))
  )
translate (p, env, (AlloyBinary Greater x y)) =
  ( env
  , SmtBinary Gt
              (second (translate (p, env, x)))
              (second (translate (p, env, y)))
  )
translate (p, env, (AlloyBinary GTE x y)) =
  ( env
  , SmtBinary Gte
              (second (translate (p, env, x)))
              (second (translate (p, env, y)))
  )
translate (_        , _  , (AlloyBinary NOT_LT _ _) ) = undefined
translate (_        , _  , (AlloyBinary NOT_LTE _ _)) = undefined
translate (_        , _  , (AlloyBinary NOT_GT _ _) ) = undefined
translate (_        , _  , (AlloyBinary NOT_GTE _ _)) = undefined
translate (_        , _  , (AlloyBinary SHL _ _)    ) = undefined
translate (_        , _  , (AlloyBinary SHA _ _)    ) = undefined
translate (_        , _  , (AlloyBinary SHR _ _)    ) = undefined

-- Translation of 'x in y' where A = translate x, B = translate Y
-- left sort | right sort | Translation
-- -------------------------------------
-- tuple     | tuple      | (= A B)
-- tuple     | set        | (member tuple set)
-- set       | set        | (subset A B)
translate (smtScript, env, (AlloyBinary IN x y)     ) = (env, auxiliaryB)
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

translate (p, env, (AlloyBinary NOT_IN x y)) = (env, SmtUnary Not expr)
  where (_, expr) = translate (p, env, AlloyBinary IN x y)
translate (p, env, (AlloyBinary AND x y)) =
  ( env
  , SmtMultiArity
    And
    [(second (translate (p, env, x))), (second (translate (p, env, y)))]
  )
translate (p, env, (AlloyBinary OR x y)) =
  ( env
  , SmtMultiArity
    Or
    [(second (translate (p, env, x))), (second (translate (p, env, y)))]
  )
translate (p, env, (AlloyBinary IFF x y)) =
  ( env
  , SmtBinary Eq
              (second (translate (p, env, x)))
              (second (translate (p, env, y)))
  )
-- if then else expression
translate (p, env, (AlloyITE c x y)) =
  ( env
  , SmtIte (second (translate (p, env, c)))
           (second (translate (p, env, x)))
           (second (translate (p, env, y)))
  )
-- quantified expression
translate (_, _, (AlloyQt _ _ _) ) = undefined
-- let expression
translate (_, _, (AlloyLet _ _ _)) = undefined
translate (_, _, AlloyList _ _   ) = undefined

-- types
translateType :: AlloyType -> Sort
translateType (Prod xs) = Set (Tuple ys)
  where ys = map (\x -> if isInt (Signature x) then UInt else Atom) xs
translateType AlloyBool = SmtBool
