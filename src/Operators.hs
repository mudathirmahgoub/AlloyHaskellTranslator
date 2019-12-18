module Operators where

data UnaryOp
    = SOMEOF -- some of
    | LONEOF -- lone of
    | ONEOF -- one of
    | SETOF -- set of
    | EXACTLYOF -- exactly of
    | NOT -- !
    | NO -- no
    | SOME -- some
    | LONE -- lone
    | ONE -- one
    | TRANSPOSE -- ~
    | RCLOSURE -- *
    | CLOSURE -- ^
    | CARDINALITY -- #
    | CAST2INT -- Int->int
    | CAST2SIGINT -- int->Int
    | NOOP -- NOOP
    deriving (Show, Eq)


data BinaryOp
    = ARROW -- ->    
    | ANY_ARROW_SOME -- ->some    
    | ANY_ARROW_ONE -- ->one
    | ANY_ARROW_LONE -- ->lone    
    | SOME_ARROW_ANY -- some->    
    | SOME_ARROW_SOME -- some->some    
    | SOME_ARROW_ONE -- some->one    
    | SOME_ARROW_LONE -- some->lone    
    | ONE_ARROW_ANY -- one->    
    | ONE_ARROW_SOME -- one->some    
    | ONE_ARROW_ONE -- one->one    
    | ONE_ARROW_LONE -- one->lone    
    | LONE_ARROW_ANY -- lone->    
    | LONE_ARROW_SOME -- lone->some    
    | LONE_ARROW_ONE -- lone->one    
    | LONE_ARROW_LONE -- lone->lone    
    | ISSEQ_ARROW_LONE -- isSeq->lone    
    | JOIN -- .    
    | DOMAIN -- <:    
    | RANGE -- :>    
    | INTERSECT -- &    
    | PLUSPLUS -- ++    
    | PLUS -- +    
    | IPLUS -- @+    
    | MINUS -- -    
    | IMINUS -- @-    
    | MUL -- *    
    | DIV -- /    
    | REM -- %    
    | EQUALS -- =    
    | NOT_EQUALS -- !=    
    | IMPLIES -- =>    
    | LT -- <    
    | LTE -- <=    
    | GT -- >    
    | GTE -- >=    
    | NOT_LT -- !<    
    | NOT_LTE -- !<=    
    | NOT_GT -- !>    
    | NOT_GTE -- !>=    
    | SHL -- <<    
    | SHA -- >>    
    | SHR -- >>>    
    | IN -- in    
    | NOT_IN -- !in    
    | AND -- &&    
    | OR -- ||    
    | IFF -- <=>
    deriving (Show, Eq)
