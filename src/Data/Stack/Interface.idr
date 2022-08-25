module Data.Stack.Interface

import Data.DPair

public export
interface STACK (Stack : Type -> Type) where
  Empty          : (Stack a) -> Type
  0 EmptyOrNot   : (s : Stack a) -> Either (Empty s) (Not (Empty s))

  empty          : (Subset (Stack a) Empty)

  isEmpty        : Stack a -> Bool
  0 isEmptyTrue  : (s : Stack a) -> (Empty s)       -> (isEmpty s === True)
  0 isEmptyFalse : (s : Stack a) -> (Not (Empty s)) -> (isEmpty s === False)
  
  cons           : a -> Stack a -> (Subset (Stack a) (Not . Empty))
  head           : (Subset (Stack a) (Not . Empty)) -> a
  tail           : (Subset (Stack a) (Not . Empty)) -> Stack a

  0 opHead       : (x : a) -> (s : Stack a) -> head (cons x s) === x
  0 opTail       : (x : a) -> (s : Stack a) -> tail (cons x s) === s
 