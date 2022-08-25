module Data.Heap.Interface

%hide Prelude.Types.elem

public export
interface Heap (heap : Type) (elem : Type) where
  Empty           : heap -> Type

  empty           : heap
  isEmpty         : (h : heap) -> Either (Empty h) (Not (Empty h))

  0 EmptyIsEmpty  : Empty empty

  insert : elem -> heap -> heap

  0 InsertNonEmpty : (e : elem) -> (h : heap) -> Not (Empty (insert e h))

  merge : heap -> heap -> heap
  0 MergeEmpty     : (h1, h2 : heap) -> Empty h1 -> Empty h2 -> Empty (merge h1 h2)
  0 MergeNonEmptyL : (h1, h2 : heap) -> (Not (Empty h1)) -> Not (Empty (merge h1 h2))
  0 MergeNonEmptyR : (h1, h2 : heap) -> (Not (Empty h2)) -> Not (Empty (merge h1 h2))

  findMin   : (h : heap) -> (0 ok : Not (Empty h)) -> elem
  deleteMin : (h : heap) -> (0 ok : Not (Empty h)) -> heap

