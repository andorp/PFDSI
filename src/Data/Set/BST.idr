module Data.Set.BST

import Data.Cert
import Decidable.Equality
import Data.TotalOrd
import Data.Set.Interface

||| Binary Search Tree
|||
||| Binary Search Trees are binary trees with elements stored at the interior nodes
||| in symmetric order, meaning that the element at any given node is greater than
||| each element in its left subtree and less than each element in its right subtree.
|||
||| Elements stored in the tree should have total ordering.
data BST e = E | T (BST e) e (BST e)

%name BST t

empty : BST e
empty = E

insert : (Ord e) => e -> BST e -> BST e
insert x E = T E x E
insert x (T t1 y t2) = case compare x y of
  LT => T (insert x t1) y t2
  EQ => T t1 y t2
  GT => T t1 y (insert x t2)

member : (Ord e) => e -> BST e -> Bool
member x E           = False
member x (T t1 y t2) = case compare x y of
  LT => member x t1
  EQ => True
  GT => member x t2

||| Property of well formed tree.
data WF : (Ord e) => BST e -> Type where
  ||| The empty tree is well-formed.
  WFe  : (Ord e) => WF (the (BST e) E)
  ||| The leaf node is well-formed.
  WFL  : (Ord e) => (x1 : e) -> WF (T E x1 E)
  ||| An intermediate node, with an empty tree on its left is well-formed if the right child of the node
  ||| is well-formed, and the element stored in the node is less than the element stored in the right child.
  WFLe : (Ord e) => (x,y   : e) -> WF (the (BST e) E) -> WF (T rl y rr)     -> compare x y === LT -> WF (T E x (T rl y rr))
  ||| An intermediate node, with an empty tree on its right is well-formed if the left child of the node
  ||| is well-formed, and the element stored in the right child is less than the element stored in the node.
  WFRe : (Ord e) => (x,y   : e) -> WF (T ll x lr)     -> WF (the (BST e) E) -> compare x y === LT -> WF (T (T ll x lr) y E)
  WFT  : (Ord e) => (x,y,z : e) -> WF (T ll x lr)     -> WF (T rl z rr)     -> compare x y === LT -> compare y z === LT -> WF (T (T ll x lr) y (T rl z rr))

wellFormedInj : (Ord e) => {x : e} -> WF (T l x r) -> (WF l, WF r)
wellFormedInj (WFL x) = (WFe, WFe)
wellFormedInj (WFLe x z w v prf) = (w, v)
wellFormedInj (WFRe y x w v prf) = (w, v)
wellFormedInj (WFT y x w v s prf prf1) = (v, s)

wellFormedRight : (Ord e) => {x,y : e} -> WF (T l x (T t y t1)) -> compare x y === LT
wellFormedRight (WFLe x y v s p)    = p
wellFormedRight (WFT z x y s u p q) = q

wellFormedLeft : (Ord e) => {x,y : e} -> WF (T (T t x t2) y r) -> compare x y === LT
wellFormedLeft (WFRe x y v s p)    = p
wellFormedLeft (WFT x y v s u p q) = p

||| Check if the given tree is well-formed.
wellFormed : (Ord e) => (t : BST e) -> Dec (WF t)
wellFormed E = Yes WFe
wellFormed (T E x E) = Yes (WFL x)
wellFormed (T E x (T t y t1)) with (wellFormed (T t y t1))
  _ | Yes ok with (compare x y) proof xy
    _ | LT = Yes (WFLe x y WFe ok xy)
    _ | EQ = No (eqNotLt xy . wellFormedRight)
    _ | GT = No (gtNotLt xy . wellFormedRight)
  _ | No nok = No (nok . snd . wellFormedInj)
wellFormed (T (T t x t2) y E) with (wellFormed (T t x t2))
  _ | Yes ok with (compare x y) proof xy
    _ | LT = Yes (WFRe x y ok WFe xy)
    _ | EQ = No (eqNotLt xy . wellFormedLeft)
    _ | GT = No (gtNotLt xy . wellFormedLeft)
  _ | No nok = No (nok . fst . wellFormedInj)
wellFormed (T (T t x t2) y (T t1 z t3)) with (wellFormed (T t x t2))
  _ | Yes lok with (wellFormed (T t1 z t3))
    _ | Yes rok with (compare x y) proof xy
      _ | LT with (compare y z) proof yz
        _ | LT = Yes (WFT x y z lok rok xy yz)
        _ | EQ = No (eqNotLt yz . wellFormedRight)
        _ | GT = No (gtNotLt yz . wellFormedRight)
      _ | EQ = No (eqNotLt xy . wellFormedLeft)
      _ | GT = No (gtNotLt xy . wellFormedLeft)
    _ | No nrok = No (nrok . snd . wellFormedInj)
  _ | No nlok = No (nlok . fst . wellFormedInj)

wfLeft : (Ord e) => {x : e} -> WF (T l x r) -> WF l
wfLeft (WFL x) = WFe
wfLeft (WFLe x z w v prf) = w
wfLeft (WFRe y x w v prf) = w
wfLeft (WFT y x w v s prf prf1) = v

wfRight : (Ord e) => {x : e} -> WF (T l x r) -> WF r
wfRight (WFL x) = WFe
wfRight (WFLe x z w v prf) = v
wfRight (WFRe y x w v prf) = v
wfRight (WFT y x w v s prf prf1) = s

InsertWFL1 : (Ord e) => (x,z : e) -> (compare x z === LT) -> WF (T rl z rr) -> WF (insert x rl) -> WF (T (insert x rl) z rr)
InsertWFL1 x z xz (WFL z) wf2 = WFRe x z wf2 WFe xz
InsertWFL1 x z xz (WFLe z w v s prf) wf2 = WFT x z w wf2 s xz prf
InsertWFL1 x z xz (WFRe y z v s prf) wf2 with (compare x y)
  _ | LT = WFRe y z wf2 s prf
  _ | EQ = WFRe y z wf2 s prf
  _ | GT = WFRe y z wf2 s prf
InsertWFL1 x z xz (WFT y z v s t prf prf1) wf2 with (compare x y)
  _ | LT = WFT y z v wf2 t prf prf1
  _ | EQ = WFT y z v wf2 t prf prf1
  _ | GT = WFT y z v wf2 t prf prf1

InsertWFL2 : (Ord e) => (x,z : e) -> (compare z x === LT) -> WF (T rl z rr) -> WF (insert x rr) -> WF (T rl z (insert x rr))
InsertWFL2 x z xz (WFL z) wf2 = WFLe z x WFe wf2 xz
InsertWFL2 x z xz (WFLe z w v s prf) wf2 with (compare x w)
  _ | LT = WFLe z w v wf2 prf
  _ | EQ = WFLe z w v wf2 prf
  _ | GT = WFLe z w v wf2 prf
InsertWFL2 x z xz (WFRe y z v s prf) wf2 = WFT y z x v wf2 prf xz
InsertWFL2 x z xz (WFT y z v s t prf prf1) wf2 with (compare x v)
  _ | LT = WFT y z v s wf2 prf prf1
  _ | EQ = WFT y z v s wf2 prf prf1
  _ | GT = WFT y z v s wf2 prf prf1

InsertWF : (TotalOrd e) => (x : e) -> (t : BST e) -> WF t -> WF (insert x t)
InsertWF x (the (BST e) E) WFe = WFL x
InsertWF x (T E y E) (WFL y) with (compare x y) proof xy
  _ | LT = WFRe x y (WFL x) WFe xy
  _ | EQ = WFL y
  _ | GT = WFLe y x WFe (WFL x) (compareGtLt x y xy)
InsertWF x (T E y (T rl z rr)) (WFLe y z w v prf) with (compare x y) proof xy
  _ | LT = WFT x y z (WFL x) v xy prf
  _ | EQ = WFLe y z w v prf
  _ | GT with (compare x z) proof xz
    _ | LT = WFLe y z w (InsertWFL1 x z xz v (InsertWF x rl (wfLeft v))) prf
    _ | EQ = WFLe y z w v prf
    _ | GT = WFLe y z w (InsertWFL2 x z (compareGtLt x z xz) v (InsertWF x rr (wfRight v))) prf
InsertWF x (T (T ll y lr) z E) (WFRe y z w v prf) with (compare x z) proof xz
  _ | LT with (compare x y) proof xy
    _ | LT = WFRe y z (InsertWFL1 x y xy w (InsertWF x ll (wfLeft w))) v prf
    _ | EQ = WFRe y z w v prf
    _ | GT = WFRe y z (InsertWFL2 x y (compareGtLt x y xy) w (InsertWF x lr (wfRight w))) v prf
  _ | EQ = WFRe y z w v prf
  _ | GT = WFT y z x w (WFL x) prf (compareGtLt x z xz)
InsertWF x (T (T ll y lr) z (T rl w rr)) (WFT y z w v s prf prf1) with (compare x z) proof xz
  _ | LT with (compare x y) proof xy
    _ | LT = WFT y z w (InsertWFL1 x y xy v (InsertWF x ll (wfLeft v))) s prf prf1
    _ | EQ = WFT y z w v s prf prf1
    _ | GT = WFT y z w (InsertWFL2 x y (compareGtLt x y xy) v (InsertWF x lr (wfRight v))) s prf prf1
  _ | EQ = WFT y z w v s prf prf1
  _ | GT with (compare x w) proof xw
    _ | LT = WFT y z w v (InsertWFL1 x w xw s (InsertWF x rl (wfLeft s))) prf prf1
    _ | EQ = WFT y z w v s prf prf1
    _ | GT = WFT y z w v (InsertWFL2 x w (compareGtLt x w xw) s (InsertWF x rr (wfRight s))) prf prf1

EmptyMember : (Ord e) => (x : e) -> member x BST.empty === False
EmptyMember x = Refl

InsertMember : (TotalOrd e) => (x : e) -> (s : BST e) -> member x (insert x s) === True
InsertMember x E = rewrite (compareEq x) in Refl
InsertMember x (T t1 y t2) with (compare x y) proof eq
  _ | LT = rewrite eq in InsertMember x t1
  _ | EQ = rewrite eq in Refl
  _ | GT = rewrite eq in InsertMember x t2

{e : Type} -> TotalOrd e => SET e (BST e) where
  empty          = BST.empty
  insert         = BST.insert
  member         = BST.member
  EmptyMember    = BST.EmptyMember
  InsertMember   = BST.InsertMember
