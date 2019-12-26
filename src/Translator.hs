module Translator where
import           Operators
import           Alloy
import           Smt
import           Env

declare :: (Env, AlloyExpr) -> (Env, SmtExpr)
declare (env, (Prime x)) = undefined 
declare x = error ("Can not declare " ++ (show x))

translate :: (Env, AlloyExpr) -> (Env, SmtExpr)
translate (env, (Prime x)) =
  if contains env (label x) then (env, get env (label x)) else declare (env, (Prime x)) 
translate (env, (Subset x)              ) = undefined
-- | Field
translate (env, (AlloyConstant name sig)) = case sig of
  SigInt -> (env, SmtIntConstant (read name))
  _      -> error ("Constant " ++ " is not supported")
translate (env, (AlloyUnary SOMEOF x)   ) = undefined
translate (env, (AlloyUnary LONEOF x)   ) = undefined
translate (env, (AlloyUnary ONEOF x)    ) = undefined
translate (env, (AlloyUnary SETOF x)    ) = undefined
translate (env, (AlloyUnary EXACTLYOF x)) = undefined
translate (env, (AlloyUnary NOT x)) =
  (env, SmtUnary NOT (second (translate (env, x))))
translate (env, (AlloyUnary NO _)       ) = undefined
translate (env, (AlloyUnary SOME _)     ) = undefined
translate (env, (AlloyUnary LONE _)     ) = undefined
translate (env, (AlloyUnary ONE _)      ) = undefined
translate (env, (AlloyUnary TRANSPOSE x)) = undefined
  where Product ys = undefined
translate (env, (AlloyUnary RCLOSURE x)   ) = undefined
translate (env, (AlloyUnary CLOSURE x)    ) = undefined
translate (env, (AlloyUnary CARDINALITY _)) = undefined
translate (env, (AlloyUnary NOOP x)       ) = translate (env, x)
-- binary expressions
translate (env, (AlloyBinary ARROW x y)   ) = undefined
 where
  Product xs = undefined
  Product ys = undefined
translate (env, (AlloyBinary ANY_ARROW_SOME x y)  ) = undefined
translate (env, (AlloyBinary ANY_ARROW_ONE x y)   ) = undefined
translate (env, (AlloyBinary ANY_ARROW_LONE x y)  ) = undefined
translate (env, (AlloyBinary SOME_ARROW_ANY x y)  ) = undefined
translate (env, (AlloyBinary SOME_ARROW_SOME x y) ) = undefined
translate (env, (AlloyBinary SOME_ARROW_ONE x y)  ) = undefined
translate (env, (AlloyBinary SOME_ARROW_LONE x y) ) = undefined
translate (env, (AlloyBinary ONE_ARROW_ANY x y)   ) = undefined
translate (env, (AlloyBinary ONE_ARROW_SOME x y)  ) = undefined
translate (env, (AlloyBinary ONE_ARROW_ONE x y)   ) = undefined
translate (env, (AlloyBinary ONE_ARROW_LONE x y)  ) = undefined
translate (env, (AlloyBinary LONE_ARROW_ANY x y)  ) = undefined
translate (env, (AlloyBinary LONE_ARROW_SOME x y) ) = undefined
translate (env, (AlloyBinary LONE_ARROW_ONE x y)  ) = undefined
translate (env, (AlloyBinary LONE_ARROW_LONE x y) ) = undefined
translate (env, (AlloyBinary ISSEQ_ARROW_LONE x y)) = undefined
translate (env, (AlloyBinary JOIN x y)) =
  ( env
  , SmtBinary JOIN (second (translate (env, x))) (second (translate (env, y)))
  )
translate (env, (AlloyBinary DOMAIN x y)) = undefined
translate (env, (AlloyBinary RANGE x y) ) = undefined
translate (env, (AlloyBinary INTERSECT x y)) =
  ( env
  , SmtBinary INTERSECT
              (second (translate (env, x)))
              (second (translate (env, y)))
  )
translate (env, (AlloyBinary PLUSPLUS x _)) = undefined
translate (env, (AlloyBinary PLUS x y)) =
  ( env
  , SmtBinary PLUS (second (translate (env, x))) (second (translate (env, y)))
  )
translate (env, (AlloyBinary IPLUS x y) ) = undefined
translate (env, (AlloyBinary MINUS x _) ) = undefined
translate (env, (AlloyBinary IMINUS x y)) = undefined
translate (env, (AlloyBinary MUL x y)   ) = undefined
translate (env, (AlloyBinary DIV x y)   ) = undefined
translate (env, (AlloyBinary REM x y)   ) = undefined
translate (env, (AlloyBinary EQUALS x y)) =
  ( env
  , SmtBinary EQUALS (second (translate (env, x))) (second (translate (env, y)))
  )
translate (env, (AlloyBinary NOT_EQUALS x y)) =
  ( env
  , SmtUnary
    NOT
    (SmtBinary EQUALS
               (second (translate (env, x)))
               (second (translate (env, y)))
    )
  )
translate (env, (AlloyBinary IMPLIES x y)) =
  ( env
  , SmtBinary IMPLIES
              (second (translate (env, x)))
              (second (translate (env, y)))
  )
translate (env, (AlloyBinary Less x y)) =
  ( env
  , SmtBinary Less (second (translate (env, x))) (second (translate (env, y)))
  )
translate (env, (AlloyBinary LTE x y)) =
  ( env
  , SmtBinary LTE (second (translate (env, x))) (second (translate (env, y)))
  )
translate (env, (AlloyBinary Greater x y)) =
  ( env
  , SmtBinary Greater
              (second (translate (env, x)))
              (second (translate (env, y)))
  )
translate (env, (AlloyBinary GTE x y)) =
  ( env
  , SmtBinary GTE (second (translate (env, x))) (second (translate (env, y)))
  )
translate (env, (AlloyBinary NOT_LT x y) ) = undefined
translate (env, (AlloyBinary NOT_LTE x y)) = undefined
translate (env, (AlloyBinary NOT_GT x y) ) = undefined
translate (env, (AlloyBinary NOT_GTE x y)) = undefined
translate (env, (AlloyBinary SHL x y)    ) = undefined
translate (env, (AlloyBinary SHA x y)    ) = undefined
translate (env, (AlloyBinary SHR x y)    ) = undefined
translate (env, (AlloyBinary IN x y)     ) = undefined
translate (env, (AlloyBinary NOT_IN x y) ) = undefined
translate (env, (AlloyBinary AND x y)) =
  ( env
  , SmtBinary AND (second (translate (env, x))) (second (translate (env, y)))
  )
translate (env, (AlloyBinary OR x y)) =
  ( env
  , SmtBinary OR (second (translate (env, x))) (second (translate (env, y)))
  )
translate (env, (AlloyBinary IFF x y)) =
  ( env
  , SmtBinary IFF (second (translate (env, x))) (second (translate (env, y)))
  )
-- if then else expression
translate (env, (AlloyITE c x y)) =
  ( env
  , SmtIte (second (translate (env, c)))
           (second (translate (env, x)))
           (second (translate (env, y)))
  )
-- quantified expression
translate (env, (AlloyQt _ x y) ) = undefined
-- let expression
translate (env, (AlloyLet _ _ x)) = undefined
