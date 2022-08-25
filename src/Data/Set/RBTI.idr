module Data.Set.RBTI

-- Intrinsic version of the red-black tree.

||| Color of a node.
|||
||| The Node can have Red or Black colors abbrevariated as R and B.
data Color = R | B

||| Indexed implementation of the red-black tree
|||
||| The indices are the element of the type we store in the tree.
||| The color of the root node of the tree.
||| The black height of the tree.
|||
||| Invariant 1:
||| Invariant 2:
data Tree : Type -> Color -> Nat -> Type where
  ||| The empty tree is Black and has 0 height.
  E  : Tree e B 0
  ||| The red node can only have black subtrees of the same black height.
  Rn : Tree e B n -> e -> Tree e B n -> Tree e R n
  ||| The both sub-trees of a black node could be red or black of the
  ||| same black height. The black height of the resulting tree is one more than
  ||| its subtrees.
  Bn : {cl, cr : Color} -> Tree e cl n -> e -> Tree e cr n -> Tree e B (S n)

-- As insert is a complicated operation on red-black trees.
-- For the implementation of the certified version of the insert on the
-- indexed version of the red-black tree, there must be many helper functions
-- needs to be introduced, as the insert operation breaks the original invariants.
namespace Insert

  ||| The invariant is violated somehow.
  |||
  ||| The 'Y' stands for Yes, an invariant is violated.
  ||| The 'N' stands for No, an invariant is not violated.
  data Violation = Y | N

  ||| Top level possible invariant violating red-black tree composion for insert. In short ITree.
  |||
  ||| Invariant violation of the red-black trees during insert and balance operation
  ||| As the violation of invariants only happen at the root node of any tree during
  ||| the insertion, this data structure holds regular Red-Black trees in its
  ||| subtrees.
  data ITree : Type -> Violation -> Color -> Nat -> Type where
    ||| Emtpy tree
    Eo : ITree e N B 0
    ||| Red node which violates the invariant in its left subtree.
    Rl : Tree e R n -> e -> Tree e B n -> ITree e Y R n
    ||| Red node which violates the invariant in its right subtree.
    Rr : Tree e B n -> e -> Tree e R n -> ITree e Y R n
    ||| Red node which does not violate any invariants.
    Ro : Tree e B n -> e -> Tree e B n -> ITree e N R n
    ||| Black node which does not violate any invariants.
    Bo : {l,r : Color} -> Tree e l n -> e -> Tree e r n -> ITree e N B (S n)

  -- data NonEmpty : (t : ITree e v c n) -> Type where
  --   NERl : NonEmpty (Rl a x b)
  --   NERr : NonEmpty (Rr a x b)
  --   NERo : NonEmpty (Ro a x b)
  --   NEBo : NonEmpty (Bo a x b)

  ||| Any well-formed red-black tree is a non violating ITree.
  mkITree : Tree e c n -> ITree e N c n
  mkITree E = Eo
  mkITree (Rn x y z) = Ro x y z
  mkITree (Bn x y z) = Bo x y z

  ||| The color of the node after the balance operation on the ITree.
  |||
  ||| The color of the resulting node must be Red when there
  ||| is violation in any of its subtrees.
  balanceColor : Color -> Violation -> Violation -> Color
  balanceColor B Y N = R
  balanceColor B N Y = R
  balanceColor c _ _ = c

  ||| The height of the node after the balance operation on the ITree.
  |||
  ||| The height for the black node must be increased. For red node it must stay the same.
  ||| This property comes from the invariants.
  balanceHeight : Color -> Nat -> Nat
  balanceHeight B n = S n
  balanceHeight R n = n

  ||| Valid argument configuration for the balance operation
  |||
  ||| The internal operation for insert insTree produces ITrees and the balance operation
  ||| must work on the result of the insTree. Although not all configuration of
  ||| the ITree subtrees are allowed, as the ITree datatype is not restrictive enough
  ||| for the balance operation. The balance function needs to restrict its arguments
  ||| and has to force the client of the balance function to provide only
  ||| valid configuration.
  |||
  ||| The constructors of this datatype represent the valid indices for the balance inputs.
  data ValidBalance : Color -> (Color, Violation) -> (Color, Violation) -> Type where
    ||| A black node is being balanced and the left subtee is a red one with violation.
    BlkVioOnFst : ValidBalance B (R,Y) (c,N)
    ||| A black node is being balanced and the right subtree is a red one with violation.
    BlkVioOnSnd : ValidBalance B (c,N) (R,Y)
    ||| A non violating black node is being balanced.
    BlkOk       : ValidBalance B (c,N) (z,N)
    ||| A non violating red node is being balanced.
    RedOK       : ValidBalance R (B,N) (B,N)
    ||| A red node has a red subtree on its left, this leads to violation.
    RedVioOnFst : ValidBalance R (R,N) (B,N)
    ||| A red node has a red subtree on its right, this leads to violation.
    RedVioOnSnd : ValidBalance R (B,N) (R,N)

  ||| The violation after the balance.
  |||
  ||| It will depend on the configuration of the arguments. Violation
  ||| is introduced, when red-red path is created.
  balanceViolation : ValidBalance c x y -> Violation
  balanceViolation BlkVioOnFst = N
  balanceViolation BlkVioOnSnd = N
  balanceViolation BlkOk       = N
  balanceViolation RedOK       = N
  balanceViolation RedVioOnFst = Y
  balanceViolation RedVioOnSnd = Y

  ||| Balancing operation.
  |||
  ||| It removes the red-red paths. Pattern matcing on all the cases are needed, because
  ||| we use indexed version of the red-black tree implementation, and only pattern
  ||| matching can reveal the actual values of the indices on the ITree data.
  ||| This may seem more verbose compared to the non-indexed version, but it also
  ||| reveals the true nature of the balance operation.
  balance
    :  (c : Color)
    -> (l : ITree e v1 c1 n) -> e -> (r : ITree e v2 c2 n)
    -> {auto v : ValidBalance c (c1,v1) (c2,v2)}
    -> ITree e (balanceViolation v) (balanceColor c v1 v2) (balanceHeight c n)
  balance B (Rl (Rn a x b) y c) z Eo         {v = BlkVioOnFst} = Ro (Bn a x b) y (Bn c z E)
  balance B (Rl (Rn a x b) y c) z (Ro l w r) {v = BlkVioOnFst} = Ro (Bn a x b) y (Bn c z (Rn l w r))
  balance B (Rl (Rn a x b) y c) z (Bo l w r) {v = BlkVioOnFst} = Ro (Bn a x b) y (Bn c z (Bn l w r))
  balance B (Rr a x (Rn b y c)) z Eo         {v = BlkVioOnFst} = Ro (Bn a x b) y (Bn c z E)
  balance B (Rr a x (Rn b y c)) z (Ro l w r) {v = BlkVioOnFst} = Ro (Bn a x b) y (Bn c z (Rn l w r))
  balance B (Rr a x (Rn b y c)) z (Bo l w r) {v = BlkVioOnFst} = Ro (Bn a x b) y (Bn c z (Bn l w r))
  balance B Eo         x (Rl (Rn b y c) z d) {v = BlkVioOnSnd} = Ro (Bn E x b) y (Bn c z d)
  balance B (Ro l w r) x (Rl (Rn b y c) z d) {v = BlkVioOnSnd} = Ro (Bn (Rn l w r) x b) y (Bn c z d)
  balance B (Bo l w r) x (Rl (Rn b y c) z d) {v = BlkVioOnSnd} = Ro (Bn (Bn l w r) x b) y (Bn c z d)
  balance B Eo         x (Rr b y (Rn c z d)) {v = BlkVioOnSnd} = Ro (Bn E x b) y (Bn c z d)
  balance B (Ro l w r) x (Rr b y (Rn c z d)) {v = BlkVioOnSnd} = Ro (Bn (Rn l w r) x b) y (Bn c z d)
  balance B (Bo l w r) x (Rr b y (Rn c z d)) {v = BlkVioOnSnd} = Ro (Bn (Bn l w r) x b) y (Bn c z d)
  balance B Eo         x Eo                  {v = BlkOk      } = Bo E x E
  balance B Eo         x (Ro E z E)          {v = BlkOk      } = Bo E x (Rn E z E)
  balance B (Ro E z E) x Eo                  {v = BlkOk      } = Bo (Rn E z E) x E
  balance B (Ro y z w) x (Ro v s t)          {v = BlkOk      } = Bo (Rn y z w) x (Rn v s t)
  balance B (Ro y z w) x (Bo v s t)          {v = BlkOk      } = Bo (Rn y z w) x (Bn v s t)
  balance B (Bo y z w) x (Ro v s t)          {v = BlkOk      } = Bo (Bn y z w) x (Rn v s t)
  balance B (Bo y z w) x (Bo v s t)          {v = BlkOk      } = Bo (Bn y z w) x (Bn v s t)
  balance R Eo         x Eo                  {v = RedOK      } = Ro E x E
  balance R (Bo y z w) x (Bo v s t)          {v = RedOK      } = Ro (Bn y z w) x (Bn v s t)
  balance R (Ro y z w) x Eo                  {v = RedVioOnFst} = Rl (Rn y z w) x E
  balance R (Ro y z w) x (Bo v s t)          {v = RedVioOnFst} = Rl (Rn y z w) x (Bn v s t)
  balance R Eo         x (Ro y z w)          {v = RedVioOnSnd} = Rr E x (Rn y z w)
  balance R (Bo y z w) x (Ro v s t)          {v = RedVioOnSnd} = Rr (Bn y z w) x (Rn v s t)

  ||| Description of valid state transtion of ITree indices in the ins operation.
  |||
  ||| As the ins operation recursively calls itself and returns an existential verion of the ITree
  ||| which is being used in the balance operation. There must be an evidence that the
  ||| returned value conforms the expected result.
  data InsResult : Type -> Color -> Nat -> Type where
    RRN : (t : ITree e N R n) -> InsResult e R n
    RRY : (t : ITree e Y R n) -> InsResult e R n
    BRN : (t : ITree e N R n) -> InsResult e B n
    BBN : (t : ITree e N B n) -> InsResult e B n

  ||| Helper function for insert
  |||
  ||| This function creates a Tree which potentionaly violates the invariant,
  ||| but it pushes the invariant violation towards the root node.
  ins : {c : Color} -> Ord e => e -> Tree e c n -> (InsResult e c n)
  ins x E = BRN (Ro E x E)
  ins x (Rn a y b) with (compare x y)
    _ | LT = case ins x a of
              (BRN a') => RRY (balance R a' y (mkITree b))
              (BBN a') => RRN (balance R a' y (mkITree b))
    _ | EQ = RRN (Ro a y b)
    _ | GT = case ins x b of
              (BRN b') => RRY (balance R (mkITree b) y b')
              (BBN b') => RRN (balance R (mkITree b) y b')
  ins x (Bn {cr} a y b) with (compare x y)
    _ | LT = case ins x a of
              (RRN a') => BBN (balance B a' y (mkITree b))
              (RRY a') => BRN (balance B a' y (mkITree b))
              (BRN a') => BBN (balance B a' y (mkITree b))
              (BBN a') => BBN (balance B a' y (mkITree b))
    _ | EQ = BBN (Bo a y b)
    _ | GT with (cr)
      _ | R = case ins x b of
                (RRN b') => BBN (balance B (mkITree a) y b')
                (RRY b') => BRN (balance B (mkITree a) y b')
      _ | B = case ins x b of
                (BRN b') => BBN (balance B (mkITree a) y b')
                (BBN b') => BBN (balance B (mkITree a) y b')

  ||| Insert an element to the red-black tree.
  export
  partial -- WHY?
  insert1 : Ord e => e -> {n : Nat} -> Tree e B n -> (m : Nat ** Tree e B m)
  insert1 x t = case (ins x t) of
    (BRN (Ro a x b)) => (_ ** Bn a x b)
    (BBN Eo)         => (_ ** E) -- TODO: Remove
    (BBN (Bo a x b)) => (_ ** Bn a x b)
