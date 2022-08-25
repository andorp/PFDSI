module Data.Stack.List

import Data.DPair
import Data.Stack.Interface


data EmptyList : (List a) -> Type where
  IsEmpty : EmptyList []

absurdEmptyList : (EmptyList (x :: xs)) -> a
absurdEmptyList IsEmpty impossible

empyList : (Subset (List a) EmptyList)
empyList = (Element [] IsEmpty)

isEmptyList : List a -> Bool
isEmptyList []        = True
isEmptyList (x :: xs) = False

isEmptyTrueStack : (s : List a) -> (EmptyList s) -> (isEmptyList s === True)
isEmptyTrueStack [] IsEmpty = Refl

isEmptyFalseStack : (s : List a) -> (Not (EmptyList s)) -> (isEmptyList s === False)
isEmptyFalseStack []        f = void (f IsEmpty)
isEmptyFalseStack (x :: xs) f = Refl

consList : a -> List a -> (Subset (List a) (Not . EmptyList))
consList x xs = Element (x :: xs) absurdEmptyList

headList : (Subset (List a) (Not . EmptyList)) -> a
headList (Element []        nonEmpty) = void (nonEmpty IsEmpty)
headList (Element (x :: xs) nonEmpty) = x

tailList : (Subset (List a) (Not . EmptyList)) -> List a
tailList (Element []        nonEmpty) = void (nonEmpty IsEmpty)
tailList (Element (x :: xs) nonEmpty) = xs

opHeadList : (x : a) -> (s : List a) -> headList (consList x s) === x
opHeadList x s = Refl

opTailList : (x : a) -> (s : List a) -> tailList (consList x s) === s
opTailList x s = Refl

emptyOrNot : (s : List a) -> Either (EmptyList s) (Not (EmptyList s))
emptyOrNot []        = Left IsEmpty
emptyOrNot (x :: xs) = Right absurdEmptyList

STACK List where
  Empty        = EmptyList
  EmptyOrNot   = emptyOrNot
  empty        = empyList
  isEmpty      = isEmptyList
  isEmptyTrue  = isEmptyTrueStack
  isEmptyFalse = isEmptyFalseStack
  cons         = consList
  head         = headList
  tail         = tailList
  opHead       = opHeadList
  opTail       = opTailList
