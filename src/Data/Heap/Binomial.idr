module Data.Heap.Binomial

import Data.Heap.Interface

data Tree e = Node Nat e (List (Tree e))

root : Tree e -> e
root (Node k x xs) = x

link : (Ord e) => Tree e -> Tree e -> Tree e
link (Node r1 x1 c1) (Node r2 x2 c2) = case x1 < x2 of
  True  => Node (S r1) x1 ((Node r2 x2 c2) :: c1)
  False => Node (S r1) x2 ((Node r1 x1 c1) :: c2)

Heap : Type -> Type
Heap e = List (Tree e)

empty : Heap e
empty = []

absurd0 : (0 _ : Void) -> a
absurd0 x impossible

data Empty : Heap e -> Type where
  IsEmpty : Empty []

absurdEmpty : Empty (x :: xs) -> Void
absurdEmpty x impossible

EmptyIsEmpty : Empty Binomial.empty
EmptyIsEmpty = IsEmpty

isEmpty : (h : Heap e) -> Either (Empty h) (Not (Empty h))
isEmpty []        = Left IsEmpty
isEmpty (x :: xs) = Right absurdEmpty

rank : Tree e -> Nat
rank (Node k x xs) = k

insTree : (Ord e) => Tree e -> Heap e -> Heap e
insTree t [] = [t]
insTree t ts@(t' :: ts') = case rank t < rank t' of
  True  => t :: ts
  False => insTree (link t t') ts'

InsTreeNonEmpty : (Ord e) => (t : Tree e) -> (h : Heap e) -> (Not (Empty (insTree t h)))
InsTreeNonEmpty t []        ae = absurdEmpty ae
InsTreeNonEmpty t (y :: xs) ae with (rank t < rank y)
  _ | True  = absurdEmpty ae
  _ | False = InsTreeNonEmpty (link t y) xs ae

insert : (Ord e) => e -> Heap e -> Heap e
insert x ts = insTree (Node 0 x []) ts

InsertNonEmpty : (Ord e) => (x : e) -> (h : Heap e) -> Not (Empty (Binomial.insert x h))
InsertNonEmpty x []        ae = absurdEmpty ae
InsertNonEmpty x (t :: ts) ae with (0 < rank t)
  _ | True  = absurdEmpty ae
  _ | False = InsTreeNonEmpty (link (Node 0 x []) t) ts ae

merge : (Ord e) => Heap e -> Heap e -> Heap e
merge ts [] = ts
merge [] ts = ts
merge ts1@(t1 :: ts1') ts2@(t2 :: ts2') = case rank t1 < rank t2 of
  True  => t1 :: merge ts1' ts2
  False => case rank t2 < rank t1 of
    True => t2 :: merge ts1 ts2'
    False => insTree (link t1 t2) (merge ts1' ts2')

MergeEmpty : (Ord e) => (h1, h2 : Heap e) -> Empty h1 -> Empty h2 -> Empty (merge h1 h2)
MergeEmpty [] [] IsEmpty IsEmpty = IsEmpty

MergeNonEmptyL : (Ord e) => (h1, h2 : Heap e) -> (Not (Empty h1)) -> Not (Empty (merge h1 h2))
MergeNonEmptyL []         h2        ne ae = ne IsEmpty
MergeNonEmptyL (y :: xs)  []        ne ae = ne ae
MergeNonEmptyL (y :: xs)  (x :: ys) ne ae with (rank y < rank x)
  _ | True  = absurdEmpty ae
  _ | False with (rank x < rank y)
    _ | True  = absurdEmpty ae
    _ | False = InsTreeNonEmpty (link y x) (merge xs ys) ae

MergeNonEmptyR : (Ord e) => (h1, h2 : Heap e) -> (Not (Empty h2)) -> Not (Empty (merge h1 h2))
MergeNonEmptyR []         []        ne ae = ne ae
MergeNonEmptyR []         (x :: xs) ne ae = ne ae
MergeNonEmptyR (y :: xs)  []        ne ae = ne IsEmpty
MergeNonEmptyR (y :: xs)  (x :: ys) ne ae with (rank y < rank x)
  _ | True  = absurdEmpty ae
  _ | False with (rank x < rank y)
    _ | True  = absurdEmpty ae
    _ | False = InsTreeNonEmpty (link y x) (merge xs ys) ae

removeMinTree : (Ord e) => (h : Heap e) -> (0 _ : Not (Empty h)) -> (Tree e, Heap e)
removeMinTree []                  ne = absurd0 (ne IsEmpty)
removeMinTree (t :: [])           ne = (t, [])
removeMinTree (t :: (x :: xs))  ne =
  let (t', ts') = removeMinTree (x :: xs) absurdEmpty
  in case (root t == root t') of
      True  => (t, x :: xs)
      False => (t', t :: x :: xs)

findMin : (Ord e) => (h : Heap e) -> (0 _ : Not (Empty h)) -> e
findMin ts ne = root (fst (removeMinTree ts ne))

deleteMin : (Ord e) => (h : Heap e) -> (0 _ : Not (Empty h)) -> Heap e
deleteMin ts ne =
  let (Node _ x ts1, ts2) = removeMinTree ts ne
  in merge (reverse ts1) ts2

{e : Type} -> Ord e => Heap (Binomial.Heap e) e where
  Empty           = Binomial.Empty
  empty           = Binomial.empty
  isEmpty         = Binomial.isEmpty
  EmptyIsEmpty    = Binomial.EmptyIsEmpty
  insert          = Binomial.insert
  InsertNonEmpty  = Binomial.InsertNonEmpty
  merge           = Binomial.merge
  MergeEmpty      = Binomial.MergeEmpty
  MergeNonEmptyL  = Binomial.MergeNonEmptyL
  MergeNonEmptyR  = Binomial.MergeNonEmptyR
  findMin         = Binomial.findMin
  deleteMin       = Binomial.deleteMin
