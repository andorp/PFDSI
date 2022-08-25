module Data.Set.RBT

import Data.Cert
import Data.OrdCert

data Color = R | B

data Tree e = E | T Color (Tree e) e (Tree e)

empty : Tree e
empty = E

%name Tree t

-- TODO: Invariants

data Empty : Tree e -> Type where
  IsEmpty : Empty E

absurdEmpty : Empty (T c a x b) -> Void
absurdEmpty e impossible

data NonEmpty : Tree e -> Type where
  IsNonEmpty : NonEmpty (T c l x r)

value : (t : Tree e) -> Not (Empty t) -> e
value E           ne = absurd (ne IsEmpty)
value (T c l x r) ne = x

mvalue : Tree e -> Maybe e
mvalue t = ?m1

left : (t : Tree e) -> Not (Empty t) -> Tree e
left E           ne = absurd (ne IsEmpty)
left (T c l x r) ne = l

right : (t : Tree e) -> Not (Empty t) -> Tree e
right E           ne = absurd (ne IsEmpty)
right (T c l x r) ne = r

member : (Ord e) => (x : e) -> Tree e -> Bool
member x E = False
member x (T _ a y b) = case compare x y of
  LT => member x a
  EQ => True
  GT => member x b

balance : Color -> Tree e -> e -> Tree e -> (t : (Tree e) ** NonEmpty t)
balance B (T R (T R a x b) y c) z d = (T R (T B a x b) y (T B c z d) ** IsNonEmpty) -- case 1
balance B (T R a x (T R b y c)) z d = (T R (T B a x b) y (T B c z d) ** IsNonEmpty) -- case 2
balance B a x (T R (T R b y c) z d) = (T R (T B a x b) y (T B c z d) ** IsNonEmpty) -- case 3
balance B a x (T R b y (T R c z d)) = (T R (T B a x b) y (T B c z d) ** IsNonEmpty) -- case 4
balance c a x b = (T c a x b ** IsNonEmpty)

insTree : (Ord e) => e -> Tree e -> (DPair (Tree e) NonEmpty)
insTree x E = (T R E x E ** IsNonEmpty)
insTree x (T c a y b) = case compare x y of
  LT => balance c (fst (insTree x a)) y b
  EQ => (T c a y b ** IsNonEmpty)
  GT => balance c a y (fst (insTree x b))

insert : (Ord e) => e -> Tree e -> Tree e
insert x t = case insTree x t of
  ((T c a y b) ** IsNonEmpty) => T B a y b

EmptyMember : (Ord e) => (x : e) -> (member x RBT.empty === False)
EmptyMember x = Refl

-- bl1 : (Ord e) => (w : e) -> (l : Tree e) -> (z : e) -> (r : Tree e) -> (ok : member w l === True) -> (member w (balance0 B l z r) === True)
-- bl1 = ?wr1

-- br1 : (Ord e) => (x : e) -> (l : Tree e) -> (z : e) -> (r : Tree e) -> (ok : member x r === True) -> (member x (fst (balance B l z r)) === True)
-- br1 = ?wr2

-- InsTreeMember : (OrdCert e) => (x : e) -> (s : Tree e) -> (member x (fst (insTree x s)) === True) 
-- InsTreeMember x E = rewrite compareEq x in Refl
-- InsTreeMember x (T R l y r) with (compare x y) proof xy
--   _ | LT = rewrite xy in InsTreeMember x l
--   _ | EQ = rewrite xy in Refl
--   _ | GT = rewrite xy in InsTreeMember x r
-- InsTreeMember x (T B l y r) with (compare x y) proof xy
--   _ | LT = bl1 x (fst (insTree x l)) y r (InsTreeMember x l)
--   _ | EQ = rewrite xy in Refl
--   _ | GT = br1 x l y (fst (insTree x r)) (InsTreeMember x r)
--             --  member x ((balance B l y ((insTree x r) .fst)) .fst) = True

-- InsertMember : (OrdCert e) => (x : e) -> (s : Tree e) -> (member x (insert x s) === True)
-- InsertMember x E = rewrite compareEq x in Refl
-- InsertMember x (T c l y r) with (compare x y) proof xy
--   _ | LT = ?InsertMember_rhs_1a
--   _ | EQ = rewrite xy in Refl
--   _ | GT = ?InsertMember_rhs_1c
















-- data Middle : (x,y,z : e) -> Type where
--   InMiddle
--     :  (Ord e)
--     => (x,y,z : e)
--     -> (Either (compare x y === LT) (compare x y === EQ))
--     -> (compare y z === GT)
--     -> Middle x y z

data LTEQ : Ord e => (x,y : e) -> Type where
  IsLT : (Ord e) => (x, y : e) -> compare x y === LT -> LTEQ x y
  IsEQ : (Ord e) => (x, y : e) -> compare x y === EQ -> LTEQ x y

data GT : Ord e => (x,y : e) -> Type where
  IsGT : (Ord e) => (x,y : e) -> compare x y === GT -> GT x y

data WellFormed : (Ord e) => Maybe e -> Tree e -> Type where
  WEm : (Ord e) => WellFormed Nothing (the (Tree e) E)
  WLf : (Ord e) => (x : e) -> WellFormed (Just x) (T c E x E)
  WLo : (Ord e) => (x : e) -> (l : Tree e) -> WellFormed (Just xl) l -> LTEQ xl x -> WellFormed (Just x) (T c l x E)
  WRo : (Ord e) => (x : e) -> (r : Tree e) -> WellFormed (Just xr) r -> GT xr x -> WellFormed (Just x) (T c E x r)
  WTr : (Ord e) => (x : e)
                -> (l : Tree e) -> WellFormed (Just xl) l
                -> (r : Tree e) -> WellFormed (Just xr) r
                -> LTEQ xl x -> GT xr x
                -> WellFormed (Just x) (T c l x r)

wellFormedInsTree : (Ord e) => (x : e) -> (t : Tree e) -> WellFormed y t -> (z : e ** WellFormed (Just z) (fst (insTree x t)))
wellFormedInsTree x (the (Tree e) E) WEm = (x ** WLf x)
wellFormedInsTree x (T R E z E) (WLf z) with (compare x z) proof xz
  _ | LT = (z ** WLo z (T R E x E) (WLf x) (IsLT x z xz))
  _ | EQ = (z ** WLf z)
  _ | GT = (z ** WRo z (T R E x E) (WLf x) (IsGT x z xz))
wellFormedInsTree x (T B E z E) (WLf z) with (compare x z) proof xz
  _ | LT = (z ** WLo z (T R E x E) (WLf x) (IsLT x z xz))
  _ | EQ = (z ** WLf z)
  _ | GT = (z ** WRo z (T R E x E) (WLf x) (IsGT x z xz))
wellFormedInsTree x (T R l z E) (WLo z l w v) with (compare x z) proof xz
  _ | LT = ?wellFormedInsTree_rhs_7a_0
  _ | EQ = (z ** WLo z l w v)
  _ | GT = (z ** WTr z l w (T R E x E) (WLf x) v (IsGT x z xz))
wellFormedInsTree x (T B l z E) (WLo z l w v) = ?wellFormedInsTree_rhs_8
wellFormedInsTree x (T R E z r) (WRo z r w v) = ?wellFormedInsTree_rhs_9
wellFormedInsTree x (T B E z r) (WRo z r w v) = ?wellFormedInsTree_rhs_10
wellFormedInsTree x (T R l z r) (WTr z l w r v s u) = ?wellFormedInsTree_rhs_11
wellFormedInsTree x (T B l z r) (WTr z l w r v s u) = ?wellFormedInsTree_rhs_12

-- wellFormed : (Ord e) => (x : e) -> (t : Tree e) -> WellFormed y t -> (z : e ** WellFormed (Just z) (insert x t))
-- wellFormed x (the (Tree e) E) WEm = (x ** WLf x)
-- wellFormed x (T R E z E) (WLf z) with (compare x z) proof xz
--   _ | LT = (z ** WLo z (T R E x E) (WLf x) (IsLT x z xz))
--   _ | EQ = (z ** WLf z)
--   _ | GT = (z ** WRo z (T R E x E) (WLf x) (IsGT x z xz))
-- wellFormed x (T B E z E) (WLf z) with (compare x z) proof xz
--   _ | LT = (z ** WLo z (T R E x E) (WLf x) (IsLT x z xz))
--   _ | EQ = (z ** WLf z)
--   _ | GT = (z ** WRo z (T R E x E) (WLf x) (IsGT x z xz))
-- wellFormed x (T R l z E) (WLo z l w v) with (compare x z) proof xz
--   _ | LT = (z ** WLo z ((insTree x l) .fst) ?wellFormed_rhs_5a_4 ?wellFormed_rhs_5a_5)
--   _ | EQ = (z ** WLo z l w v)
--   _ | GT = (z ** WTr z l w (T R E x E) (WLf x) v (IsGT x z xz))
-- wellFormed x (T B l z E) (WLo z l w v) = ?wellFormed_rhs_6
-- wellFormed x (T R E z r) (WRo z r w v) = ?wellFormed_rhs_7
-- wellFormed x (T B E z r) (WRo z r w v) = ?wellFormed_rhs_8
-- wellFormed x (T R l z r) (WTr z l w r v s u) = ?wellFormed_rhs_9
-- wellFormed x (T B l z r) (WTr z l w r v s u) = ?wellFormed_rhs_10

-- EmptyMember  : (Ord e) => (x : e) -> (member x RBT.empty === False)
-- EmptyMember x = Refl

-- absurdTrueFalse : (True === False) -> Void
-- absurdTrueFalse x impossible

-- absurdFalseTrue : (False === True) -> Void
-- absurdFalseTrue x impossible

-- nonEmptyLeftOrRight
--   :  (Ord e)
--   => (x : e) -> (t : Tree e) -> (member x t === True) -> (ne : Not (Empty t))
--   -> Tri (     value t ne === x , member x (left t ne) === False, member x (right t ne) === False)
--          (Not (value t ne === x), member x (left t ne) === True , member x (right t ne) === False)
--          (Not (value t ne === x), member x (left t ne) === False, member x (right t ne) === False)
-- nonEmptyLeftOrRight = ?w0

-- BalanceMemberLeftA : (Ord e) => (x : e) -> (c : Color) -> (l : Tree e) -> (y : e) -> (r : Tree e) -> (member x l === True) -> member x (fst (balance c l y r)) === True
-- BalanceMemberLeftA x c l y r prf = ?BalanceMemberLeftA_rhs

-- BalanceMemberLeft : (Ord e) => (x : e) -> (c : Color) -> (l : Tree e) -> (y : e) -> (r : Tree e) -> (member x l === True) -> member x (fst (balance c l y r)) === True
-- BalanceMemberLeft x R l y r prf with (compare x y)
--   _ | LT = prf
--   _ | EQ = Refl
--   _ | GT = ?BalanceMemberLeft_rhs_0b
-- BalanceMemberLeft x B l y r prf = ?BalanceMemberLeft_rhs_1

-- BalanceMemberRight : (Ord e) => (x : e) -> (c : Color) -> (l : Tree e) -> (y : e) -> (r : Tree e) -> (member x r === True) -> member x (fst (balance c l y r)) === True
-- BalanceMemberRight x R l y r prf with (compare x y)
--   _ | LT = ?i1
--   _ | EQ = Refl
--   _ | GT = prf
-- BalanceMemberRight x B l y r prf = ?BalanceMemberRight_rhs_1

-- lessThanLeft : (Ord e) => (x,y : e) -> (compare x y === LT) -> (member x l === True) -> member x (T c l y r) === True
-- lessThanLeft = ?lt1

-- greaterThanRight : (Ord e) => (x,y : e) -> (compare x y === GT) -> member x r === True -> member x (T c l y r) === True
-- greaterThanRight = ?gt1

-- InsTreeMember : (OrdCert e) => (x : e) -> (s : Tree e) -> (member x (fst (insTree x s)) === True)
-- InsTreeMember x E = rewrite compareEq x in Refl
-- InsTreeMember x (T c l y r) with (compare x y) proof cxy
--   _ | LT = ?w3 -- lessThanLeft x y cxy ?w1
--   _ | EQ = ?w1 -- rewrite eqxy in Refl
--   _ | GT = ?w2 -- BalanceMemberRight x c l y (fst (insTree x r)) (InsTreeMember x r)

-- -- InsertMember : (OrdCert e) => (x : e) -> (s : Tree e) -> (member x (fst (insert x s)) === True)
-- -- InsertMember x E = rewrite compareEq x in Refl
-- -- InsertMember x (T y t z t1) with (compare x z)
-- --   -- _ | LT = ?w0 -- member x ((case balance y ((insTree x t) .fst) z t1 of { (E ** ne) => absurd (ne IsEmpty) ; (T c a y b ** ne) => (T B a y b ** absurdEmpty) }) .fst) = True
-- --   _ | LT = ?w0
-- --   -- _ | LT with (balance y ((insTree x t) .fst) z t1)
-- --   --   _ | (E ** ne) = absurd (ne IsEmpty)
-- --   --   _ | (T xc xl xv xr ** ne) = ?w3
-- --   _ | EQ = ?w1
-- --   _ | GT = ?w2
