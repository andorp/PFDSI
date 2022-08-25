module Data.Stack

namespace NonSafeInterface1

  interface STACK where
    constructor MkStack
    Stack   : Type -> Type
    empty   : Stack a
    isEmpty : Stack a -> Bool
    cons    : a -> Stack a -> Stack a
    head    : Stack a -> a
    tail    : Stack a -> Stack a

  partial
  STACK where
    Stack = List
    empty = []
    isEmpty = \case
                [] => True
                (x :: xs) => False
    cons = (::)
    head = \case
              (x :: xs) => x
    tail = id

namespace NonSafeInterface0

  interface STACK (Stack : Type -> Type) where
    constructor MkStack
    empty   : Stack a
    isEmpty : Stack a -> Bool
    cons    : a -> Stack a -> Stack a
    head    : Stack a -> a
    tail    : Stack a -> Stack a

  partial
  NonSafeInterface0.STACK List where
    empty = []
    isEmpty = \case
                [] => True
                (x :: xs) => False
    cons = (::)
    head = \case
              (x :: xs) => x
    tail = id

namespace NonSafeRecord

  record STACK where
    constructor MkStack
    Stack   : Type -> Type
    empty   : {a : Type} -> Stack a
    isEmpty : {a : Type} -> Stack a -> Bool
    cons    : {a : Type} -> a -> Stack a -> Stack a
    head    : {a : Type} -> Stack a -> a
    tail    : {a : Type} -> Stack a -> Stack a

  partial
  list : NonSafeRecord.STACK
  list = MkStack
    { Stack = List
    , empty = []
    , isEmpty = \case
                  [] => True
                  (x :: xs) => False
    , cons = (::)
    , head = \case
                (x :: xs) => x
    , tail = id
    }

data EmptyList : (List a) -> Type where
  IsEmpty : EmptyList []

data NonEmptyList : (List a) -> Type where
  IsNonEmpty : NonEmptyList (x :: xs)

emptyStack : (xs : List a ** EmptyList xs)
emptyStack = ([] ** IsEmpty)

isEmptyStack : List a -> Bool
isEmptyStack []        = True
isEmptyStack (x :: xs) = False

isEmptyTrueStack : (s : List a) -> (EmptyList s) -> (isEmptyStack s === True)
isEmptyTrueStack [] IsEmpty = Refl

isEmptyFalseStack : (s : List a) -> (NonEmptyList s) -> (isEmptyStack s === False)
isEmptyFalseStack (_ :: _) IsNonEmpty = Refl

consStack : a -> List a -> (s : List a ** (NonEmptyList s))
consStack x xs = (x :: xs ** IsNonEmpty)

headStack : (s : List a ** NonEmptyList s) -> a
headStack ((x :: xs) ** IsNonEmpty) = x

tailStack : (s : List a ** NonEmptyList s) -> List a
tailStack ((x :: xs) ** IsNonEmpty) = xs

opHeadStack : (x : a) -> (s : List a) -> headStack (consStack x s) === x
opHeadStack x s = Refl

opTailStack : (x : a) -> (s : List a) -> tailStack (consStack x s) === s
opTailStack x s = Refl

impossibleNonEmptyList : NonEmptyList [] -> Void
impossibleNonEmptyList IsNonEmpty impossible

impossibleEmptyList : EmptyList (x :: xs) -> Void
impossibleEmptyList IsEmpty impossible

eitherEmptyStack : (s : List a) -> Either (EmptyList s, Not (NonEmptyList s)) (NonEmptyList s, Not (EmptyList s))
eitherEmptyStack []        = Left  (IsEmpty, impossibleNonEmptyList)
eitherEmptyStack (x :: xs) = Right (IsNonEmpty, impossibleEmptyList)

namespace SafeRecord

  record STACK where
    constructor MkStack
    Stack        : Type -> Type
    Empty        : {a : Type} -> (Stack a) -> Type
    NonEmpty     : {a : Type} -> (Stack a) -> Type
    eitherEmpty  : {a : Type} -> (s : Stack a) -> Either (Empty s, Not (NonEmpty s)) (NonEmpty s, Not (Empty s))
    
    empty        : {a : Type} -> (s : Stack a ** Empty s)
    
    isEmpty      : {a : Type} -> Stack a -> Bool
    isEmptyTrue  : {a : Type} -> (s : Stack a) -> (Empty s)    -> (isEmpty s === True)
    isEmptyFalse : {a : Type} -> (s : Stack a) -> (NonEmpty s) -> (isEmpty s === False)
    
    cons         : {a : Type} -> a -> Stack a -> (s : Stack a ** (NonEmpty s))
    head         : {a : Type} -> (s : Stack a ** NonEmpty s) -> a
    tail         : {a : Type} -> (s : Stack a ** NonEmpty s) -> Stack a

    opHead       : {a : Type} -> (x : a) -> (s : Stack a) -> head (cons x s) === x
    opTail       : {a : Type} -> (x : a) -> (s : Stack a) -> tail (cons x s) === s

  list : SafeRecord.STACK
  list = MkStack
    { Stack         = List
    , Empty         = EmptyList
    , NonEmpty      = NonEmptyList
    , eitherEmpty   = eitherEmptyStack
    , empty         = emptyStack
    , isEmpty       = isEmptyStack
    , isEmptyTrue   = isEmptyTrueStack
    , isEmptyFalse  = isEmptyFalseStack
    , cons          = consStack
    , head          = headStack
    , tail          = tailStack
    , opHead        = opHeadStack
    , opTail        = opTailStack
    }

namespace SafeInterface0

  interface STACK (Stack : Type -> Type) where
    Empty        : (Stack a) -> Type
    NonEmpty     : (Stack a) -> Type
    0 eitherEmpty  : (s : Stack a) -> Either (Empty s, Not (NonEmpty s)) (NonEmpty s, Not (Empty s))
    
    empty        : (s : Stack a ** Empty s)
    
    isEmpty      : Stack a -> Bool
    0 isEmptyTrue  : (s : Stack a) -> (Empty s)    -> (isEmpty s === True)
    0 isEmptyFalse : (s : Stack a) -> (NonEmpty s) -> (isEmpty s === False)
    
    cons         : a -> Stack a -> (s : Stack a ** (NonEmpty s))
    head         : (s : Stack a ** NonEmpty s) -> a
    tail         : (s : Stack a ** NonEmpty s) -> Stack a

    0 opHead       : (x : a) -> (s : Stack a) -> head (cons x s) === x
    0 opTail       : (x : a) -> (s : Stack a) -> tail (cons x s) === s

  SafeInterface0.STACK List where
    Empty        = EmptyList
    NonEmpty     = NonEmptyList
    eitherEmpty  = eitherEmptyStack
    empty        = emptyStack
    isEmpty      = isEmptyStack
    isEmptyTrue  = isEmptyTrueStack
    isEmptyFalse = isEmptyFalseStack
    cons         = consStack
    head         = headStack
    tail         = tailStack
    opHead       = opHeadStack
    opTail       = opTailStack
