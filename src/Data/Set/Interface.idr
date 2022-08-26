module Data.Set.Interface

public export
interface SET (Elem : Type) (Set : Type) where
  empty  : Set
  insert : Elem -> Set -> Set
  member : Elem -> Set -> Bool

  0 EmptyMember  : (e : Elem)              -> (member e empty        === False)
  0 InsertMember : (e : Elem) -> (s : Set) -> (member e (insert e s) === True)
