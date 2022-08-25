module Data.Heap.Leftish

import Data.Heap.Interface

public export
data Heap e
  = E
  | T Nat e (Heap e) (Heap e)

public export
empty : Heap e
empty = E

public export
data Empty : (Heap a) -> Type where
  IsEmpty : Empty E

absurdEmpty : Empty (T r n a b) -> Void
absurdEmpty empty impossible

isEmpty : (h : Heap e) -> Either (Empty h) (Not (Empty h))
isEmpty E           = Left  IsEmpty
isEmpty (T k x y z) = Right absurdEmpty

rank : Heap e -> Nat
rank E           = 0
rank (T r _ _ _) = r

makeT : e -> Heap e -> Heap e -> Heap e
makeT x a b = case rank a >= rank b of
  False => T (S (rank a)) x b a
  True  => T (S (rank b)) x a b

merge : (Ord e) => Heap e -> Heap e -> Heap e
merge h E = h
merge E h = h
merge h1@(T r1 x a1 b1) h2@(T r2 y a2 b2) = case x < y of
  False => makeT y a2 (merge h1 b2)
  True  => makeT x a1 (merge b1 h2)

insert : (Ord e) => e -> Heap e -> Heap e
insert x h = merge (T 1 x E E) h

absurd0 : (0 _ : Void) -> a
absurd0 v impossible

findMin : (h : Heap e) -> (0 _ : Not (Empty h)) -> e
findMin E           ne = absurd0 (ne IsEmpty)
findMin (T k x y z) ne = x

deleteMin : (Ord e) => (h : Heap e) -> (0 _ : Not (Empty h)) -> Heap e
deleteMin E           ne = absurd0 (ne IsEmpty)
deleteMin (T _ x a b) ne = merge a b 

EmptyIsEmpty : Empty Leftish.empty
EmptyIsEmpty = IsEmpty

InsertNonEmpty : (Ord e) => (x : e) -> (h : Heap e) -> Not (Leftish.Empty (insert x h))
InsertNonEmpty x E ae = absurdEmpty ae
InsertNonEmpty x (T k y z w) ae with (x < y)
  _ | False with (rank z >= rank (merge (T 1 x E E) w))
    _ | True  = absurdEmpty ae
    _ | False = absurdEmpty ae
  _ | True with (0 < k)
    _ | True  = absurdEmpty ae
    _ | False = absurdEmpty ae

MergeEmpty : (Ord e) => (h1, h2 : Heap e) -> Empty h1 -> Empty h2 -> Empty (Leftish.merge h1 h2)
MergeEmpty E E IsEmpty IsEmpty = IsEmpty

MergeNonEmptyL : (Ord e) => (h1, h2 : Heap e) -> (Not (Empty h1)) -> Not (Empty (Leftish.merge h1 h2))
MergeNonEmptyL E           E            ne ae = ne ae
MergeNonEmptyL E           (T k x y z)  ne ae = absurdEmpty ae
MergeNonEmptyL (T k x y z) E            ne ae = ne ae
MergeNonEmptyL (T k x y z) (T j w v s)  ne ae with (x < w)
  _ | False with (rank v >= rank (merge (T k x y z) s))
    _ | False = absurdEmpty ae
    _ | True  = absurdEmpty ae
  _ | True with (rank y >= rank (merge z (T j w v s)))
    _ | False = absurdEmpty ae
    _ | True  = absurdEmpty ae

MergeNonEmptyR : (Ord e) => (h1, h2 : Heap e) -> (Not (Empty h2)) -> Not (Empty (Leftish.merge h1 h2))
MergeNonEmptyR E            E           ne ae = ne IsEmpty
MergeNonEmptyR E            (T k y z w) ne ae = ne ae
MergeNonEmptyR (T k y z w)  E           ne ae = ne IsEmpty
MergeNonEmptyR (T k y z w)  (T j v s t) ne ae with (y < v)
  _ | False with (rank s >= rank (merge (T k y z w) t))
    _ | False = absurdEmpty ae
    _ | True  = absurdEmpty ae
  _ | True with (rank z >= rank (merge w (T j v s t)))
    _ | False = absurdEmpty ae
    _ | True  = absurdEmpty ae

{e : Type} -> Ord e => Interface.Heap (Leftish.Heap e) e where
  Empty           = Leftish.Empty
  empty           = Leftish.empty
  isEmpty         = Leftish.isEmpty
  EmptyIsEmpty    = Leftish.EmptyIsEmpty
  insert          = Leftish.insert
  InsertNonEmpty  = Leftish.InsertNonEmpty
  merge           = Leftish.merge
  MergeEmpty      = Leftish.MergeEmpty
  MergeNonEmptyL  = Leftish.MergeNonEmptyL
  MergeNonEmptyR  = Leftish.MergeNonEmptyR
  findMin         = Leftish.findMin
  deleteMin       = Leftish.deleteMin
