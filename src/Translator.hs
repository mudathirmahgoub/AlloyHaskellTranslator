{-# LANGUAGE RecordWildCards #-}
module Translator where
import           AlloyOperators
import           SmtOperators
import           Alloy
import           Smt
import           Env

import           Data.List

translateModel :: AlloyModel -> SmtProgram
translateModel model = program6
 where
  sigs     = signatures model
  program1 = declareSignatures emptyProgram sigs
  program2 = translateSignatures program1 sigs
  program3 = translateSignatureFacts program2 sigs
  program4 = translateFacts program3 (facts model)
  -- axioms for none, univAtom, univInt, intValue
  program5 = addSpecialAssertions program4
  program6 = translateCommands program5 (commands model)

translateSignatures :: SmtProgram -> [Sig] -> SmtProgram
--translateSignatures p [] = p
translateSignatures p xs = translateHierarchy p (filter isTopLevel xs)

declareSignatures :: SmtProgram -> [Sig] -> SmtProgram
declareSignatures p xs = foldl declareSignature p xs

declareSignature :: SmtProgram -> Sig -> SmtProgram
declareSignature p Univ      = addConstant p univAtom
declareSignature p SigInt    = addConstant p univInt
declareSignature p None      = addConstant p none
declareSignature p SigString = undefined
declareSignature p sig       = addConstant
  p
  Variable { name = label sig, sort = Set (Tuple [s]), isOriginal = True }
  where s = if isInt (Signature sig) then UInt else Atom

translateHierarchy :: SmtProgram -> [Sig] -> SmtProgram
translateHierarchy p xs = foldl translateSignature p xs

translateSignature :: SmtProgram -> Sig -> SmtProgram
translateSignature p Univ         = p
translateSignature p SigInt       = p
translateSignature p None         = p
translateSignature p SigString    = undefined
translateSignature p PrimSig {..} = program5
 where
  program0 = foldl translateSignature p children
  program1 = translateMultiplicity program0 PrimSig { .. }
  program2 = translateParent program1 PrimSig { .. }
  program3 = translateDisjointChildren program2 PrimSig { .. }
  program4 = translateAbstract program3 PrimSig { .. }
  program5 = translateFields program4 PrimSig { .. }

translateSignature p SubsetSig {..} = program3
 where
  program1 = translateMultiplicity p SubsetSig { .. }
  program2 = translateParent program1 SubsetSig { .. }
  program3 = translateFields program2 SubsetSig { .. }

-- require sig is already defined in SMTScript p
translateMultiplicity :: SmtProgram -> Sig -> SmtProgram
-- sig a
-- use different from empty set
translateMultiplicity p sig = addAssertion assertion p
 where
  c           = getConstant p (label sig)
  s           = if isInt (Signature sig) then UInt else Atom
  x           = Variable { name = "x", sort = s, isOriginal = False }
  singleton   = (SmtUnary Singleton (SmtMultiArity MkTuple [Var x]))
  isSingleton = SmtBinary Eq (Var c) singleton
  subset      = SmtBinary Subset (Var c) singleton
  empty       = SmtUnary EmptySet (SortExpr (Set (Tuple [s])))
  existsOne   = SmtQuantified Exists [x] isSingleton
  existsSome  = SmtQuantified Exists [x] subset
  or          = SmtMultiArity Or [existsOne, empty]
  assertion   = case (multiplicity sig) of
    ONEOF  -> Assertion ("one " ++ (label sig)) existsOne
    LONEOF -> Assertion ("lone " ++ (label sig)) or
    SOMEOF -> Assertion ("some " ++ (label sig)) existsSome
    _      -> Assertion "" smtTrue

-- refactor this with subset 
translateParent :: SmtProgram -> Sig -> SmtProgram
translateParent p PrimSig {..} = addAssertion assertion p
 where
  childVar  = getConstant p primLabel
  parentVar = getConstant p (label parent)
  subset    = SmtBinary Subset (Var childVar) (Var parentVar)
  assertion = Assertion ("parent " ++ primLabel) subset

translateParent p SubsetSig {..} = addAssertion assertion p
 where
  childVar   = getConstant p subsetLabel
  parentVars = map (getConstant p . label) parents
  function parentVar = SmtBinary Subset (Var childVar) (Var parentVar)
  subsets   = SmtMultiArity And (map function parentVars)
  assertion = Assertion ("parents " ++ subsetLabel) subsets

translateDisjointChildren :: SmtProgram -> Sig -> SmtProgram
translateDisjointChildren p PrimSig {..} = addAssertion assertion p
 where
  function (x, y) = SmtBinary Eq
                              empty
                              (SmtBinary Intersection (Var xVar) (Var yVar))
   where
    xVar = getConstant p (label x)
    yVar = getConstant p (label y)
  disjointChildren zs = map function zs
  sigSort   = if isInt (Signature PrimSig { .. }) then UInt else Atom
  empty     = SmtUnary EmptySet (SortExpr (Set (Tuple [sigSort])))
  pairs     = [ (u, v) | u <- children, v <- children, (label u) < (label v) ]
  andExpr   = SmtMultiArity And (disjointChildren pairs)
  assertion = Assertion ("disjoint children of " ++ primLabel) andExpr
translateDisjointChildren p sig =
  error ((label sig) ++ " is not a prime signature")

translateAbstract :: SmtProgram -> Sig -> SmtProgram
translateAbstract p PrimSig {..} = case isAbstract && not (null children) of
  False -> p
  True  -> addAssertion assertion p
   where
    function x y = SmtBinary Union x y
    sigVar    = getConstant p primLabel
    union     = foldl function empty variables
    variables = map (Var . getConstant p . label) children
    sigSort   = if isInt (Signature PrimSig { .. }) then UInt else Atom
    empty     = SmtUnary EmptySet (SortExpr (Set (Tuple [sigSort])))
    equal     = SmtBinary Eq (Var sigVar) union
    assertion = Assertion ("Abstract " ++ primLabel) equal
translateAbstract p sig = error ((label sig) ++ " is not a prime signature")

translateFields :: SmtProgram -> Sig -> SmtProgram
translateFields p sig = program3
 where
  sigFields = fields sig
  program1  = declareFields p sigFields
  program2  = translateDisjointFields program1 sigFields
  program3  = translateDisjoint2Fields program2 sigFields

declareFields :: SmtProgram -> [Decl] -> SmtProgram
declareFields p decls = foldl declareField p decls

declareField :: SmtProgram -> Decl -> SmtProgram
declareField p decl = addConstant
  p
  Variable { name = "field", sort = Set (Tuple [Atom]), isOriginal = True }
    where sorts = typeof expr

translateDisjointFields :: SmtProgram -> [Decl] -> SmtProgram
translateDisjointFields p field = p -- ToDo: fix this

translateDisjoint2Fields :: SmtProgram -> [Decl] -> SmtProgram
translateDisjoint2Fields p field = p -- ToDo: fix this

translateSignatureFacts :: SmtProgram -> [Sig] -> SmtProgram
translateSignatureFacts p [] = p
translateSignatureFacts p xs = foldl translateSignatureFact p xs

translateSignatureFact :: SmtProgram -> Sig -> SmtProgram
translateSignatureFact p sig = case (sigfacts sig) of
  []     -> p
  x : xs -> undefined

translateFacts :: SmtProgram -> [Fact] -> SmtProgram
translateFacts p xs = foldl translateFact p xs

translateFact :: SmtProgram -> Fact -> SmtProgram
translateFact program (Fact label alloyExpr) = addAssertion assertion program
 where
  assertion    = Assertion label smtExpr
  (_, smtExpr) = translate (program, [], alloyExpr)

addSpecialAssertions :: SmtProgram -> SmtProgram
addSpecialAssertions p = p -- ToDo: change this later

translateCommands :: SmtProgram -> [Command] -> SmtProgram
translateCommands p xs = foldl translateCommand p xs

translateCommand :: SmtProgram -> Command -> SmtProgram
translateCommand p c = undefined

translate :: (SmtProgram, Env, AlloyExpr) -> (Env, SmtExpr)
translate (p, env, Signature x             ) = (env, get env (label x))
-- Field
translate (p, env, (AlloyConstant name sig)) = case sig of
  SigInt -> (env, SmtIntConstant (read name))
  _      -> error ("Constant " ++ " is not supported")
translate (p, env, (AlloyUnary SOMEOF x)   ) = undefined
translate (p, env, (AlloyUnary LONEOF x)   ) = undefined
translate (p, env, (AlloyUnary ONEOF x)    ) = undefined
translate (p, env, (AlloyUnary SETOF x)    ) = undefined
translate (p, env, (AlloyUnary EXACTLYOF x)) = undefined
translate (p, env, (AlloyUnary NOT x)) =
  (env, SmtUnary Not (second (translate (p, env, x))))
translate (p, env, (AlloyUnary NO _)                 ) = undefined
translate (p, env, (AlloyUnary SOME _)               ) = undefined
translate (p, env, (AlloyUnary LONE _)               ) = undefined
translate (p, env, (AlloyUnary ONE _)                ) = undefined
translate (p, env, (AlloyUnary TRANSPOSE x)          ) = undefined
translate (p, env, (AlloyUnary RCLOSURE x)           ) = undefined
translate (p, env, (AlloyUnary CLOSURE x)            ) = undefined
translate (p, env, (AlloyUnary CARDINALITY _)        ) = undefined
translate (p, env, (AlloyUnary NOOP x)               ) = translate (p, env, x)
-- binary expressions
translate (p, env, (AlloyBinary ARROW x y)           ) = undefined
translate (p, env, (AlloyBinary ANY_ARROW_SOME x y)  ) = undefined
translate (p, env, (AlloyBinary ANY_ARROW_ONE x y)   ) = undefined
translate (p, env, (AlloyBinary ANY_ARROW_LONE x y)  ) = undefined
translate (p, env, (AlloyBinary SOME_ARROW_ANY x y)  ) = undefined
translate (p, env, (AlloyBinary SOME_ARROW_SOME x y) ) = undefined
translate (p, env, (AlloyBinary SOME_ARROW_ONE x y)  ) = undefined
translate (p, env, (AlloyBinary SOME_ARROW_LONE x y) ) = undefined
translate (p, env, (AlloyBinary ONE_ARROW_ANY x y)   ) = undefined
translate (p, env, (AlloyBinary ONE_ARROW_SOME x y)  ) = undefined
translate (p, env, (AlloyBinary ONE_ARROW_ONE x y)   ) = undefined
translate (p, env, (AlloyBinary ONE_ARROW_LONE x y)  ) = undefined
translate (p, env, (AlloyBinary LONE_ARROW_ANY x y)  ) = undefined
translate (p, env, (AlloyBinary LONE_ARROW_SOME x y) ) = undefined
translate (p, env, (AlloyBinary LONE_ARROW_ONE x y)  ) = undefined
translate (p, env, (AlloyBinary LONE_ARROW_LONE x y) ) = undefined
translate (p, env, (AlloyBinary ISSEQ_ARROW_LONE x y)) = undefined
translate (p, env, (AlloyBinary JOIN x y)) =
  ( env
  , SmtBinary Join
              (second (translate (p, env, x)))
              (second (translate (p, env, y)))
  )
translate (p, env, (AlloyBinary DOMAIN x y)) = undefined
translate (p, env, (AlloyBinary RANGE x y) ) = undefined
translate (p, env, (AlloyBinary INTERSECT x y)) =
  ( env
  , SmtBinary Intersection
              (second (translate (p, env, x)))
              (second (translate (p, env, y)))
  )
translate (p, env, (AlloyBinary PLUSPLUS x _)) = undefined
translate (p, env, (AlloyBinary PLUS x y)) =
  ( env
  , SmtBinary Union
              (second (translate (p, env, x)))
              (second (translate (p, env, y)))
  )
translate (p, env, (AlloyBinary IPLUS x y) ) = undefined
translate (p, env, (AlloyBinary MINUS x _) ) = undefined
translate (p, env, (AlloyBinary IMINUS x y)) = undefined
translate (p, env, (AlloyBinary MUL x y)   ) = undefined
translate (p, env, (AlloyBinary DIV x y)   ) = undefined
translate (p, env, (AlloyBinary REM x y)   ) = undefined
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
translate (p, env, (AlloyBinary NOT_LT x y) ) = undefined
translate (p, env, (AlloyBinary NOT_LTE x y)) = undefined
translate (p, env, (AlloyBinary NOT_GT x y) ) = undefined
translate (p, env, (AlloyBinary NOT_GTE x y)) = undefined
translate (p, env, (AlloyBinary SHL x y)    ) = undefined
translate (p, env, (AlloyBinary SHA x y)    ) = undefined
translate (p, env, (AlloyBinary SHR x y)    ) = undefined
translate (p, env, (AlloyBinary IN x y)     ) = undefined
translate (p, env, (AlloyBinary NOT_IN x y) ) = undefined
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
translate (p, env, (AlloyQt _ x y) ) = undefined
-- let expression
translate (p, env, (AlloyLet _ _ x)) = undefined
