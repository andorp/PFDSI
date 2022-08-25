module Data.Set.BSTIntr

import Data.DPair -- Exists
import Data.TotalOrd

data LessThan : (TotalOrd e) => Maybe e -> Maybe e -> Type where
  LeafLeft  : TotalOrd e => {x : e} -> LessThan Nothing  (Just x)
  LeafRight : TotalOrd e => {x : e} -> LessThan (Just x) Nothing
  NodeLT    : TotalOrd e => {x,y : e} -> (compare x y === LT) -> LessThan (Just x) (Just y)

||| Binary Search Tree
|||
||| Binary Search Trees are binary trees with elements stored at the interior nodes
||| in symmetric order, meaning that the element at any given node is greater than
||| each element in its left subtree and less than each element in its right subtree.
|||
||| Intrinsic representation of the expected shape of the tree. The interior nodes
||| hold the proofs mentioned above. The encoding of this property requires to
||| propagate information from the subtrees to the node, for that reason
||| the tree needs to be indexed with its optional element stored in the node.
||| The users should use the BST which is an existential type.
|||
||| Elements stored in the tree should have total ordering.
data BSTCtx : (e : Type) -> (TotalOrd e) => (Maybe e) -> Type where
  E : (TotalOrd e) => BSTCtx e Nothing
  T : (TotalOrd e)
      => (BSTCtx e lx) -> (x : e) -> (BSTCtx e rx)
      -> (0 left  : LessThan lx (Just x))
      -> (0 right : LessThan (Just x) rx)
      -> BSTCtx e (Just x)

BST : (e : Type) -> (TotalOrd e) => Type
BST e = Exists (BSTCtx e)

mutual

  export
  insert : (TotalOrd e) => (x : e) -> BST e -> BST e
  insert x (Evidence Nothing E) = Evidence (Just x) (T E x E LeafLeft LeafRight)
  insert x (Evidence (Just y) (T l y r left right)) with (compare x y) proof xy
    _ | LT = Evidence _ (T (snd (insert x (Evidence _ l))) y r (lessThanLeft x y xy l left) right)
    _ | EQ = Evidence _ (T l y r left right)
    _ | GT = Evidence _ (T l y (snd (insert x (Evidence _ r))) left (lessThanRight x y xy r right))

  lessThanRight
    :  (TotalOrd e)
    => (x,y : e)
    -> (compare x y === GT)
    -> (r : BSTCtx e rx)
    -> LessThan (Just y) rx
    -> LessThan (Just y) (fst (insert x (Evidence rx r)))
  lessThanRight x y xy E lt = NodeLT (compareGtLt x y xy)
  lessThanRight x y xy (T z w v left right) lt with (compare x w)
    _ | LT = lt
    _ | EQ = lt
    _ | GT = lt

  lessThanLeft
    :  (TotalOrd e)
    => (x,y : e)
    -> (compare x y === LT)
    -> (l : BSTCtx e lx)
    -> LessThan lx (Just y)
    -> LessThan (fst (insert x (Evidence lx l))) (Just y)
  lessThanLeft x y xy E lt = NodeLT xy
  lessThanLeft x y xy (T z w v left right) lt with (compare x w)
    _ | LT = lt
    _ | EQ = lt
    _ | GT = lt
