{-# LANGUAGE RecordWildCards #-}
module Translator where
import           Operators
import           Alloy
import           Smt
import           Env

translateModel :: AlloyModel -> SmtProgram
translateModel model = program6
 where
  -- none, univAtom, univInt, intValue
  program1 = addconstants emptyProgram [none, univAtom, idenAtom, univInt]
  program2 = translateSignatures program1 (signatures model)
  program3 = translateSignatureFacts program2 (signatures model)
  program4 = translateFacts program3 (facts model)
  -- axioms for none, univAtom, univInt, intValue
  program5 = addSpecialAssertions program4
  program6 = translateCommands program5 (commands model)

translateSignatures :: SmtProgram -> [Sig] -> SmtProgram
translateSignatures p [] = p
translateSignatures p xs = program
  where program = translateTopLevelSignatures p (filter isTopLevel xs)

translateTopLevelSignatures :: SmtProgram -> [Sig] -> SmtProgram
translateTopLevelSignatures p xs = foldl translateSignature p xs

translateSignature :: SmtProgram -> Sig -> SmtProgram
translateSignature p Univ = p
translateSignature p SigInt = p
translateSignature p None = p
translateSignature p SigString = undefined
translateSignature p PrimSig{..} = program2
  where program1 = addconstant p Variable {name = label PrimSig{..}, sort = Set (Tuple [Atom]) , isOriginal = True}
        program2 = translateMultiplicity program1 PrimSig{..}
        program3 = translateParent program2 PrimSig{..}
        program4 = translateChildren program3 PrimSig{..}


translateMultiplicity :: SmtProgram -> Sig -> SmtProgram
translateMultiplicity p PrimSig{..} = addAssertion assertion p  
  where f = getConstant p (label PrimSig{..})  
        s = if isInt (Signature PrimSig{..}) then UInt else Atom
        x = Variable {name = "x", sort = s, isOriginal  = False}         
        exists   = SmtQuantified Exists [x] (SmtBinary EQUALS (Var f) (SmtUnary Singleton (SmtMultiArity MkTuple [Var x])))
        emptySet = SmtUnary EmptySet (SortExpr (Set (Tuple[s])))
        assertion = case (multiplicity PrimSig{..}) of
            ONEOF -> Assertion "multiplicity constraint" exists

translateParent :: SmtProgram -> Sig -> SmtProgram
translateParent = undefined

translateChildren :: SmtProgram -> Sig -> SmtProgram
translateChildren = undefined

translateSignatureFacts :: SmtProgram -> [Sig] -> SmtProgram
translateSignatureFacts p xs = foldl translateSignatureFact p xs

translateSignatureFact :: SmtProgram -> Sig -> SmtProgram
translateSignatureFact p x = undefined

translateFacts :: SmtProgram -> [Fact] -> SmtProgram
translateFacts p xs = foldl translateFact p xs

translateFact :: SmtProgram -> Fact -> SmtProgram
translateFact program (Fact label alloyExpr) = addAssertion assertion program
 where
  assertion    = Assertion label smtExpr
  (_, smtExpr) = translate (program, [], alloyExpr)

addSpecialAssertions :: SmtProgram -> SmtProgram
addSpecialAssertions p = undefined

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
  (env, SmtUnary NOT (second (translate (p, env, x))))
translate (p, env, (AlloyUnary NO _)       ) = undefined
translate (p, env, (AlloyUnary SOME _)     ) = undefined
translate (p, env, (AlloyUnary LONE _)     ) = undefined
translate (p, env, (AlloyUnary ONE _)      ) = undefined
translate (p, env, (AlloyUnary TRANSPOSE x)) = undefined
  where Product ys = undefined
translate (p, env, (AlloyUnary RCLOSURE x)   ) = undefined
translate (p, env, (AlloyUnary CLOSURE x)    ) = undefined
translate (p, env, (AlloyUnary CARDINALITY _)) = undefined
translate (p, env, (AlloyUnary NOOP x)       ) = translate (p, env, x)
-- binary expressions
translate (p, env, (AlloyBinary ARROW x y)   ) = undefined
 where
  Product xs = undefined
  Product ys = undefined
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
  , SmtBinary JOIN
              (second (translate (p, env, x)))
              (second (translate (p, env, y)))
  )
translate (p, env, (AlloyBinary DOMAIN x y)) = undefined
translate (p, env, (AlloyBinary RANGE x y) ) = undefined
translate (p, env, (AlloyBinary INTERSECT x y)) =
  ( env
  , SmtBinary INTERSECT
              (second (translate (p, env, x)))
              (second (translate (p, env, y)))
  )
translate (p, env, (AlloyBinary PLUSPLUS x _)) = undefined
translate (p, env, (AlloyBinary PLUS x y)) =
  ( env
  , SmtBinary PLUS
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
  , SmtBinary EQUALS
              (second (translate (p, env, x)))
              (second (translate (p, env, y)))
  )
translate (p, env, (AlloyBinary NOT_EQUALS x y)) =
  ( env
  , SmtUnary
    NOT
    (SmtBinary EQUALS
               (second (translate (p, env, x)))
               (second (translate (p, env, y)))
    )
  )
translate (p, env, (AlloyBinary IMPLIES x y)) =
  ( env
  , SmtBinary IMPLIES
              (second (translate (p, env, x)))
              (second (translate (p, env, y)))
  )
translate (p, env, (AlloyBinary Less x y)) =
  ( env
  , SmtBinary Less
              (second (translate (p, env, x)))
              (second (translate (p, env, y)))
  )
translate (p, env, (AlloyBinary LTE x y)) =
  ( env
  , SmtBinary LTE
              (second (translate (p, env, x)))
              (second (translate (p, env, y)))
  )
translate (p, env, (AlloyBinary Greater x y)) =
  ( env
  , SmtBinary Greater
              (second (translate (p, env, x)))
              (second (translate (p, env, y)))
  )
translate (p, env, (AlloyBinary GTE x y)) =
  ( env
  , SmtBinary GTE
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
  , SmtBinary AND
              (second (translate (p, env, x)))
              (second (translate (p, env, y)))
  )
translate (p, env, (AlloyBinary OR x y)) =
  ( env
  , SmtBinary OR
              (second (translate (p, env, x)))
              (second (translate (p, env, y)))
  )
translate (p, env, (AlloyBinary IFF x y)) =
  ( env
  , SmtBinary IFF
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
