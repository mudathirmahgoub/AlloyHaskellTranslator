module SmtOperators where


data SmtUnaryOp
    = Not
    | Complement
    | Transpose
    | TClosure
    | Singleton
    | UnivSet
    | EmptySet
    deriving (Show, Eq)

data SmtBinaryOp
    = Implies
    | Plus
    | Minus
    | Multiply
    | Divide
    | Mod
    | Eq
    | Gte
    | Lte
    | Gt
    | Lt
    | Union
    | Intersection
    | SetMinus
    | Member
    | Subset
    | Join
    | Product
    | TupSel
    deriving (Show, Eq)

data SmtQuantifier = Exists | ForAll  deriving (Show, Eq)

data SmtMultiArityOp
    = MkTuple
    | Insert
    | Distinct
    | And
    | Or
    deriving (Show, Eq)
