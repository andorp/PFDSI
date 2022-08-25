module Data.Set.RBT2

import Data.Cert
import Data.TotalOrd
import Decidable.Equality

data Color = R | B

absurdColor : Not (R = B)
absurdColor rb impossible

mutual

  data Node e = N Color (Tree e) e (Tree e)

  data Tree e = E | T (Node e)

absurdTree : Not (T x === E)
absurdTree x impossible

nodeInj : {l1,l2,r1,r2 : Tree e} -> {x1,x2 : e} -> {c1,c2 : Color} -> N c1 l1 x1 r1 === N c2 l2 x2 r2 -> (c1 === c2, l1 === l2, x1 === x2, r1 === r2)
nodeInj Refl = (Refl, Refl, Refl, Refl)

treeNodeInj : {l1,l2,r1,r2 : Tree e} -> {x1,x2 : e} -> {c1,c2 : Color} -> T (N c1 l1 x1 r1) === T (N c2 l2 x2 r2) -> (c1 === c2, l1 === l2, x1 === x2, r1 === r2)
treeNodeInj Refl = (Refl, Refl, Refl, Refl)

mutual

  value : Tree e -> Maybe e
  value E = Nothing
  value (T (N c l x r)) = Just x

  color : Tree e -> Color
  color E = B
  color (T (N c l x r)) = c

empty : Tree e
empty = E

%name Tree t

-- TODO: Invariants

data Empty : Tree e -> Type where
  IsEmpty : Empty E

absurdEmpty : Empty (T n) -> Void
absurdEmpty e impossible

data NonEmpty : Tree e -> Type where
  IsNonEmpty : NonEmpty (T n)

left : (t : Tree e) -> Not (Empty t) -> Tree e
left E               ne = absurd (ne IsEmpty)
left (T (N c l x r)) ne = l

right : (t : Tree e) -> Not (Empty t) -> Tree e
right E               ne = absurd (ne IsEmpty)
right (T (N c l x r)) ne = r

member : (Ord e) => (x : e) -> Tree e -> Bool
member x E = False
member x (T (N _ a y b)) = case compare x y of
  LT => member x a
  EQ => True
  GT => member x b

balance : Node e -> Node e
balance (N B (T (N R (T (N R a x b)) y c)) z d) = (N R (T (N B a x b)) y (T (N B c z d)))
balance (N B (T (N R a x (T (N R b y c)))) z d) = (N R (T (N B a x b)) y (T (N B c z d)))
balance (N B a x (T (N R (T (N R b y c)) z d))) = (N R (T (N B a x b)) y (T (N B c z d)))
balance (N B a x (T (N R b y (T (N R c z d))))) = (N R (T (N B a x b)) y (T (N B c z d)))
balance (N c a x b) = (N c a x b)

insTree : (Ord e) => e -> Tree e -> DPair (Tree e) NonEmpty
insTree x E = (T (N R E x E) ** IsNonEmpty)
insTree x (T (N c a y b)) = case compare x y of
  LT => (T (balance (N c (fst (insTree x a)) y b)) ** IsNonEmpty)
  EQ => (T (N c a y b) ** IsNonEmpty)
  GT => (T (balance (N c a y (fst (insTree x b)))) ** IsNonEmpty)

insert : (Ord e) => e -> Tree e -> Tree e
insert x t = case insTree x t of
  ((T (N c a y b)) ** IsNonEmpty) => T (N B a y b)

insTree0 : (Ord e) => e -> Tree e -> (Tree e)
insTree0 x E = T (N R E x E)
insTree0 x (T (N c a y b)) = case compare x y of
  LT => T (balance (N c (insTree0 x a) y b))
  EQ => T (N c a y b)
  GT => T (balance (N c a y (insTree0 x b)))

insert0 : (Ord e) => e -> Tree e -> Tree e
insert0 x t = case insTree0 x t of
  E => E -- Stupid
  (T (N c a y b)) => T (N B a y b)

EmptyMember : (Ord e) => (x : e) -> (member x RBT2.empty === False)
EmptyMember x = Refl

data LessThan : (TotalOrd e) => Maybe e -> Maybe e -> Type where
  LeafLeft  : TotalOrd e => {x : e} -> LessThan Nothing  (Just x)
  LeafRight : TotalOrd e => {x : e} -> LessThan (Just x) Nothing
  NodeLT    : TotalOrd e => {x,y : e} -> (compare x y === LT) -> LessThan (Just x) (Just y)

data WRBT : (e : Type) -> (TotalOrd e) => (t : Tree e) -> Color -> (Maybe e) -> Nat -> Type where
  WE  : TotalOrd e => WRBT e E B Nothing Z
  WBN : TotalOrd e => (x : e)
                   -> (wl : WRBT e l (color l) (value l) n)
                   -> (wr : WRBT e r (color r) (value r) n)
                   -> (lx : LessThan (value l) (Just x))
                   -> (xr : LessThan (Just x) (value r))
                   -> WRBT e (T (N B l x r)) B (Just x) (S n)
  WRN : TotalOrd e => (x : e) 
                   -> (wl : WRBT e l B (value l) n)
                   -> (wr : WRBT e r B (value r) n)
                   -> (cl : color l === B)
                   -> (cr : color r === B)
                   -> (lx : LessThan (value l) (Just x))
                   -> (xr : LessThan (Just x) (value r))
                   -> WRBT e (T (N R l x r)) R (Just x) n

wrtbInj : TotalOrd e => WRBT e t c x n -> (color t === c, value t === x)
wrtbInj WE                        = (Refl, Refl)
wrtbInj (WBN x wl wr lx xr)       = (Refl, Refl)
wrtbInj (WRN x wl wr cl cr lx xr) = (Refl, Refl)

WellFormed : {e : Type} -> TotalOrd e => Color -> Tree e -> Type
WellFormed c t = (n : Nat ** WRBT e t c (value t) n)

wellFormedRedLeft : TotalOrd e => WRBT e (T (N R l x r)) R (Just x) n -> WRBT e l B (value l) n
wellFormedRedLeft (WRN x l r lb rb lx xr) = l

wellFormedBlackLeft : TotalOrd e => WRBT e (T (N B l x r)) B (Just x) (S n) -> WRBT e l (color l) (value l) n
wellFormedBlackLeft (WBN _ l r lx xr) = l

wellFormedRedLessThan : TotalOrd e => WRBT e (T (N R (T (N B ll x lr)) y (T (N B rl z rr)))) R (Just y) n -> (compare x y === LT, compare y z === LT)
wellFormedRedLessThan (WRN y wl wr cl cr (NodeLT xl) (NodeLT xr)) = (xl, xr)

wellFormedBlackLessThan : TotalOrd e => WRBT e (T (N B (T (N cl ll x lr)) y (T (N cr rl z rr)))) B (Just y) n -> (compare x y === LT, compare y z === LT)
wellFormedBlackLessThan (WBN y wl wr (NodeLT xy) (NodeLT yz)) = (xy, yz)

wellFormedBlackLessThanCase1 : TotalOrd e => WRBT e (T (N B E y (T (N R E z E)))) B (Just y) n -> compare y z === LT
wellFormedBlackLessThanCase1 (WBN y wl wr lx (NodeLT yz)) = yz

wellFormedLessThanLeft : TotalOrd e => WRBT e (T (N c (T (N cl ll x lr)) y r)) c (Just y) n -> compare x y === LT
wellFormedLessThanLeft (WBN y wl wr       (NodeLT xy) xr) = xy
wellFormedLessThanLeft (WRN y wl wr cl cr (NodeLT xy) xr) = xy

wellFormedLessThanLeft0 : TotalOrd e => WRBT e (T (N c (T (N cl ll x lr)) y r)) c (Just y) n -> LessThan (Just x) (Just y)
wellFormedLessThanLeft0 (WBN y wl wr lx xr) = lx
wellFormedLessThanLeft0 (WRN y wl wr prf cr lx xr) = lx

wellFormedLessThanRight : TotalOrd e => WRBT e (T (N c l x (T (N cr rl y rr)))) c (Just x) n -> compare x y === LT
wellFormedLessThanRight (WBN x wl wr       lx (NodeLT xy)) = xy
wellFormedLessThanRight (WRN x wl wr cl cr lx (NodeLT xy)) = xy

wellFormedLessThanRight0 : TotalOrd e => WRBT e (T (N c l x (T (N cr rl y rr)))) c (Just x) n -> LessThan (Just x) (Just y)
wellFormedLessThanRight0 (WBN x wl wr lx xr) = xr
wellFormedLessThanRight0 (WRN x wl wr cl prf lx xr) = xr

sameBlackDepth : (TotalOrd e) => WRBT e t c x n -> WRBT e t c x k -> n === k
sameBlackDepth WE WE = Refl
sameBlackDepth (WBN z wl wr lx xr) (WBN z w v s u)
  = case (sameBlackDepth wl w, sameBlackDepth wr v) of
      (y, y1) => rewrite y in Refl
sameBlackDepth (WRN z wl wr cl cr lx xr) (WRN z w v prf cr1 s u)
  = case (sameBlackDepth wl w, sameBlackDepth wr v) of
      (y, y1) => y

wellFormedRedNode
  :  TotalOrd e
  => WRBT e (T (N R (T (N B ll x lr)) y (T (N B rl z rr)))) R (Just y) n
  -> (WRBT e (T (N B ll x lr)) B (Just x) n, WRBT e (T (N B rl z rr)) B (Just z) n)
wellFormedRedNode (WRN y wl wr cl cr lx xr) = (wl, wr)

wellFormedBlackNode
  :  TotalOrd e
  => WRBT e (T (N B (T (N cl ll x lr)) y (T (N cr rl z rr)))) B (Just y) (S n)
  -> (WRBT e (T (N cl ll x lr)) cl (Just x) n, WRBT e (T (N cr rl z rr)) cr (Just z) n)
wellFormedBlackNode (WBN y wl wr lx xr) = (wl, wr)

absurdBlackNode : TotalOrd e => WRBT e (T (N R l y r)) B v (S k) -> Void
absurdBlackNode wt impossible

-- -- TODO: Get better absurd functions
-- absurdRedRedRight : TotalOrd e => WRBT e (T (N R l y (T (N R rl z rr)))) R (Just y) n -> Void
-- absurdRedRedRight (WRN _ _ WE                      _ _ _ _) impossible
-- absurdRedRedRight (WRN _ _ (WBN x l r lx xr)       _ _ _ _) impossible
-- absurdRedRedRight (WRN _ _ (WRN x l r lb rb lx xr) _ _ _ _) impossible

-- absurdRedRedLeft : TotalOrd e => WRBT e (T (N R (T (N R ll x lr)) y r)) R (Just y) n -> Void
-- absurdRedRedLeft (WRN _ WE                      _ _ _ _ _) impossible
-- absurdRedRedLeft (WRN _ (WBN x l r lx xr)       _ _ _ _ _) impossible
-- absurdRedRedLeft (WRN _ (WRN x l r lb rb lx xr) _ _ _ _ _) impossible

-- absurdZeroBlack : TotalOrd e => WRBT e (T (N B l x r)) B (Just x) 0 -> Void
-- absurdZeroBlack WE impossible
-- absurdZeroBlack (WBN x l r lx xr) impossible
-- absurdZeroBlack (WRN x l r lx xr) impossible

-- absurdUnbalancedRight : TotalOrd e => WRBT e (T (N R E y (T (N B rl z rr)))) R (Just y) n -> Void
-- absurdUnbalancedRight (WRN _ _ WE _ _ _ _) impossible
-- absurdUnbalancedRight (WRN _ _ (WBN x l r       t u) _ _ _ _) impossible
-- absurdUnbalancedRight (WRN _ _ (WRN x l r cl cr t u) _ _ _ _) impossible
-- absurdUnbalancedRight (WRN _ WE _ _ _ _ _) impossible
-- absurdUnbalancedRight (WRN _ (WBN x l r       t u) _ _ _ _ _) impossible
-- absurdUnbalancedRight (WRN _ (WRN x l r cl cr t u) _ _ _ _ _) impossible

-- absurdUnbalancedLeft : TotalOrd e => WRBT e (T (N R (T (N B ll x lr)) y E)) R (Just y) n -> Void
-- absurdUnbalancedLeft (WRN _ WE                        WE _ _ _ _) impossible
-- absurdUnbalancedLeft (WRN _ (WBN z wl wr w v)         WE _ _ _ _) impossible
-- absurdUnbalancedLeft (WRN _ (WRN z wl wr prf cr1 w v) WE _ _ _ _) impossible

-- absurdBlackBlackRight : TotalOrd e => WRBT e (T (N B E y (T (N B rl z rr)))) B (Just y) n -> Void
-- absurdBlackBlackRight (WBN _ WE                        (WBN _ _ _ _ _) _ _) impossible
-- absurdBlackBlackRight (WBN _ (WBN x wl wr       lx xr) (WBN _ _ _ _ _) _ _) impossible
-- absurdBlackBlackRight (WBN _ (WRN x wl wr cl cr lx xr) (WBN _ _ _ _ _) _ _) impossible

-- absurdBlackBlackLeft : TotalOrd e => WRBT e (T (N B (T (N B ll x lr)) y E)) B (Just y) n -> Void
-- absurdBlackBlackLeft (WBN _ WE                      WE _ _) impossible
-- absurdBlackBlackLeft (WBN _ (WBN z wl wr w v)       WE _ _) impossible
-- absurdBlackBlackLeft (WBN _ (WRN z wl wr cl cr w v) WE _ _) impossible

-- absurdBlackRedBlack : TotalOrd e => WRBT e (T (N B E y (T (N R E z (T (N B l w r)))))) B (Just y) n -> Void
-- absurdBlackRedBlack (WBN _ WE (WRN _ WE WE                        _ _ _ _) _ _) impossible
-- absurdBlackRedBlack (WBN _ WE (WRN _ WE (WBN x wl wr       lx xr) _ _ _ _) _ _) impossible
-- absurdBlackRedBlack (WBN _ WE (WRN _ WE (WRN x wl wr cl cr lx xr) _ _ _ _) _ _) impossible

-- absurdBlackRedRed : TotalOrd e => WRBT e (T (N B ll y (T (N R rl z (T (N R l w r)))))) B (Just y) n -> Void
-- absurdBlackRedRed (WBN _ _ (WRN _ _ WE                           _ _ _ _) _ _) impossible
-- absurdBlackRedRed (WBN _ _ (WRN _ _ (WBN x u wr lx1 xr1)         _ _ _ _) _ _) impossible
-- absurdBlackRedRed (WBN _ _ (WRN _ _ (WRN x u wr prf cr1 lx1 xr1) _ _ _ _) _ _) impossible

-- absurdBlackRRedLRed : TotalOrd e => WRBT e (T (N B (T (N R ll x (T (N R t w t1)))) y rr)) B (Just y) n -> Void
-- absurdBlackRRedLRed (WBN _ (WRN _ _ WE                            _ _ _ _) _ _ _) impossible
-- absurdBlackRRedLRed (WBN _ (WRN _ _ (WBN z v wr1 lx1 xr1)         _ _ _ _) _ _ _) impossible
-- absurdBlackRRedLRed (WBN _ (WRN _ _ (WRN z v wr1 prf cr1 lx1 xr1) _ _ _ _) _ _ _) impossible

-- absurdBlackRedLRed : TotalOrd e => WRBT e (T (N B ll y (T (N R (T (N R l w r)) z rr)))) B (Just y) n -> Void
-- absurdBlackRedLRed (WBN _ _ (WRN _ WE                          _ _ _ _ _) _ _) impossible
-- absurdBlackRedLRed (WBN _ _ (WRN _ (WBN x v u lx1 xr1)         _ _ _ _ _) _ _) impossible
-- absurdBlackRedLRed (WBN _ _ (WRN _ (WRN x v u prf cr1 lx1 xr1) _ _ _ _ _) _ _) impossible

-- absurdBlackLRedBlack : TotalOrd e => WRBT e (T (N B E y (T (N R (T (N B l w r)) z rr)))) B (Just y) n -> Void
-- absurdBlackLRedBlack (WBN _ WE (WRN _ WE                         _ _ _ _ _) _ _) impossible
-- absurdBlackLRedBlack (WBN _ WE (WRN _ (WBN x wl t u xr1)         _ _ _ _ _) _ _) impossible
-- absurdBlackLRedBlack (WBN _ WE (WRN _ (WRN x wl t prf cr1 u xr1) _ _ _ _ _) _ _) impossible

-- absurdBlackLRedRightBlack : TotalOrd e =>  WRBT e (T (N B (T (N R E x (T (N B t w t1)))) y E)) B (Just y) n -> Void
-- absurdBlackLRedRightBlack (WBN _ (WRN _ WE WE                           _ _ _ _) _ _ _) impossible
-- absurdBlackLRedRightBlack (WBN _ (WRN _ WE (WBN z wl v lx1 xr1)         _ _ _ _) _ _ _) impossible
-- absurdBlackLRedRightBlack (WBN _ (WRN _ WE (WRN z wl v prf cr1 lx1 xr1) _ _ _ _) _ _ _) impossible

-- absurdBlackLRedC : TotalOrd e => WRBT e (T (N B (T (N R (T (N c t w t1)) x E)) y E)) B (Just y) n -> Void
-- absurdBlackLRedC (WBN _ (WRN _ WE                             _ _ _ _ _) _ _ _) impossible
-- absurdBlackLRedC (WBN _ (WRN _ (WBN z wl wr1 lx1 xr1)         _ _ _ _ _) _ _ _) impossible
-- absurdBlackLRedC (WBN _ (WRN _ (WRN z wl wr1 prf cr1 lx1 xr1) _ _ _ _ _) _ _ _) impossible

-- absurdBlackRedEmpty : TotalOrd e => WRBT e (T (N B (T (N R (T z) x (T w))) y E)) B (Just y) n -> Void
-- absurdBlackRedEmpty (WBN _ (WRN _ WE                           _ _ _ _ _) WE _ _) impossible
-- absurdBlackRedEmpty (WBN _ (WRN _ (WBN v wl u lx1 xr1)         _ _ _ _ _) WE _ _) impossible
-- absurdBlackRedEmpty (WBN _ (WRN _ (WRN v wl u prf cr1 lx1 xr1) _ _ _ _ _) WE _ _) impossible

-- wellFormed : (TotalOrd e) => (t : Tree e) -> Dec (n : Nat ** WRBT e t (color t) (value t) n)
-- wellFormed E
--   = Yes (0 ** WE)

-- wellFormed (T (N R E y E))
--   = Yes (0 ** WRN y WE WE Refl Refl LeafLeft LeafRight)

-- wellFormed (T (N R E y (T (N R rl z rr))))
--   = No (\(n ** arg) => absurdRedRedRight arg)

-- wellFormed (T (N R E y (T (N B rl z rr))))
--   = No (\(n ** arg) => absurdUnbalancedRight arg) 

-- wellFormed (T (N R (T (N R ll x lr)) y E))                
--   = No (\(n ** arg) => absurdRedRedLeft arg)

-- wellFormed (T (N R (T (N B ll x lr)) y E))                
--   = No (\(n ** arg) => absurdUnbalancedLeft arg)

-- wellFormed (T (N R (T (N R ll x lr)) y (T (N R rl z rr))))
--   = No (\(n ** arg) => absurdRedRedRight arg)

-- wellFormed (T (N R (T (N R ll x lr)) y (T (N B rl z rr))))
--   = No (\(n ** arg) => absurdRedRedLeft arg)

-- wellFormed (T (N R (T (N B ll x lr)) y (T (N R rl z rr))))
--   = No (\(n ** arg) => absurdRedRedRight arg)

-- wellFormed (T (N R (T (N B ll x lr)) y (T (N B rl z rr)))) with (compare x y) proof xy
--   _ | LT with (compare y z) proof yz
--     _ | LT = case (wellFormed (T (N B ll x lr)), wellFormed (T (N B rl z rr))) of
--               ((Yes (n ** lok)), (Yes (m ** rok))) =>
--                 case decEq n m of
--                   (Yes Refl) => Yes (m ** WRN y lok rok Refl Refl (NodeLT xy) (NodeLT yz))
--                   (No nnm) => No (\(k ** arg) =>
--                     case (wellFormedRedNode arg) of
--                       (absurdlok, absurdrok) =>
--                         case (sameBlackDepth absurdlok lok, sameBlackDepth absurdrok rok) of
--                           (Refl, Refl) => nnm Refl)
--               ((Yes lok), (No rnok)) => No (\(n ** arg) => rnok (n ** (snd (wellFormedRedNode arg))))
--               ((No lnok), _)         => No (\(n ** arg) => lnok (n ** (fst (wellFormedRedNode arg))))
--     _ | EQ = No (\(n ** arg) => (eqNotLt yz (snd (wellFormedRedLessThan arg))))
--     _ | GT = No (\(n ** arg) => (gtNotLt yz (snd (wellFormedRedLessThan arg))))
--   _ | EQ = No (\(n ** arg) => eqNotLt xy (fst (wellFormedRedLessThan arg)))
--   _ | GT = No (\(n ** arg) => gtNotLt xy (fst (wellFormedRedLessThan arg)))

-- wellFormed (T (N B E y E))
--   = Yes (1 ** WBN y WE WE LeafLeft LeafRight)

-- wellFormed (T (N B E y (T (N R E z E)))) with (compare y z) proof yz
--   _ | LT = Yes (1 ** WBN y WE (WRN z WE WE Refl Refl LeafLeft LeafRight) LeafLeft (NodeLT yz))
--   _ | EQ = No (\(S n ** arg) => eqNotLt yz (wellFormedBlackLessThanCase1 arg))
--   _ | GT = No (\(S n ** arg) => gtNotLt yz (wellFormedBlackLessThanCase1 arg))

-- wellFormed (T (N B E y (T (N R E z (T (N R l w r))))))
--   = No (\(S n ** arg) => absurdBlackRedRed arg)

-- wellFormed (T (N B E y (T (N R E z (T (N B l w r))))))
--   = No (\(S n ** arg) => absurdBlackRedBlack arg)

-- wellFormed (T (N B E y (T (N R (T (N R l w r)) z E))))
--   = No (\(S n ** arg) => absurdBlackRedLRed arg)

-- wellFormed (T (N B E y (T (N R (T (N B l w r)) z E))))
--   = No (\(S n ** arg) => absurdBlackLRedBlack arg)

-- wellFormed (T (N B E y (T (N R (T (N R t v t1)) z (T (N w t2 s t3))))))
--   = No (\(S n ** arg) => absurdBlackRedLRed arg)

-- wellFormed (T (N B E y (T (N R (T (N B t v t1)) z (T (N R t2 s t3))))))
--   = No (\(S n ** arg) => absurdBlackRedRed arg)

-- wellFormed (T (N B E y (T (N R (T (N B t v t1)) z (T (N B t2 s t3))))))
--   = No (\(S n ** arg) => absurdBlackLRedBlack arg)

-- wellFormed (T (N B E y (T (N B rl z rr))))
--   = No (\(S n ** arg) => absurdBlackBlackRight arg)

-- wellFormed (T (N B (T (N R E x E)) y E)) with (compare x y) proof xy
--   _ | LT = Yes (_ ** WBN y (WRN x WE WE Refl Refl LeafLeft LeafRight) WE (NodeLT xy) LeafRight)
--   _ | EQ = No (\(n ** arg) => eqNotLt xy (wellFormedLessThanLeft arg))
--   _ | GT = No (\(n ** arg) => gtNotLt xy (wellFormedLessThanLeft arg))

-- wellFormed (T (N B (T (N R E x (T (N R t w t1)))) y E))
--   = No (\(S n ** arg) => absurdBlackRRedLRed arg)

-- wellFormed (T (N B (T (N R E x (T (N B t w t1)))) y E))
--   = No (\(S n ** arg) => absurdBlackLRedRightBlack arg)

-- wellFormed (T (N B (T (N R (T (N R t w t1)) x E)) y E))
--   = No (\(S n ** arg) => absurdBlackLRedC arg)

-- wellFormed (T (N B (T (N R (T (N B t w t1)) x E)) y E))
--   = No (\(S n ** arg) => absurdBlackLRedC arg)

-- wellFormed (T (N B (T (N R (T z) x (T w))) y E))
--   = No (\(S n ** arg) => absurdBlackRedEmpty arg)

-- wellFormed (T (N B (T (N B ll x lr)) y E))
--   = No (\(S n ** arg) => absurdBlackBlackLeft arg)

-- wellFormed (T (N B (T (N cl ll x lr)) y (T (N cr rl z rr)))) with (compare x y) proof xy
--   _ | LT with (compare y z) proof yz
--     _ | LT = case (wellFormed (T (N cl ll x lr)), wellFormed (T (N cr rl z rr))) of
--         ((Yes (n ** lok)), (Yes (m ** rok))) => case decEq n m of
--           Yes Refl => Yes (S m ** WBN y lok rok (NodeLT xy) (NodeLT yz))
--           No nnm => No (\(S n ** arg) => case (wellFormedBlackNode arg) of
--             (absurdlok, absurdrok) => case (sameBlackDepth absurdlok lok, sameBlackDepth absurdrok rok) of
--               (Refl, Refl) => nnm Refl)
--         ((Yes lok), (No rnok)) => No (\(S n ** arg) => rnok (n ** (snd (wellFormedBlackNode arg))))
--         ((No lnok), v)         => No (\(S n ** arg) => lnok (n ** (fst (wellFormedBlackNode arg))))
--     _ | EQ = No (\(S n ** arg) => eqNotLt yz (snd (wellFormedBlackLessThan arg)))
--     _ | GT = No (\(S n ** arg) => gtNotLt yz (snd (wellFormedBlackLessThan arg)))
--   _ | EQ = No (\(S n ** arg) => eqNotLt xy (fst (wellFormedBlackLessThan arg)))
--   _ | GT = No (\(S n ** arg) => gtNotLt xy (fst (wellFormedBlackLessThan arg)))

-- balanceTreeCase1
--   : TotalOrd e
--   => (a,b,c,d : Tree e)
--   -> WRBT e a B (value a) n
--   -> WRBT e b B (value b) n
--   -> WRBT e c B (value c) n
--   -> WRBT e d B (value d) n
--   -> (x,y,z : e)
--   -> LessThan (value a) (Just x)
--   -> LessThan (Just x) (value b)
--   -> LessThan (Just x) (Just y)
--   -> LessThan (Just y) (value c)
--   -> LessThan (value c) (Just z)
--   -> LessThan (Just y) (Just z)
--   -> LessThan (Just z) (value d)
--   -> WRBT e (T (balance (N B (T (N R (T (N R a x b)) y c)) z d))) R (Just y) (S n)
-- balanceTreeCase1 a b c d wa wb wc wd x y z ltaxx ltxbx ltxy ltycx ltcxz ltyz ltzdx
--   = case (wrtbInj wa, wrtbInj wb, wrtbInj wc, wrtbInj wd) of
--       ((ca, Refl), (cb, Refl), (cc, Refl), (cd, Refl))
--         => WRN y
--             (WBN x (rewrite ca in wa) (rewrite cb in wb) ltaxx ltxbx)
--             (WBN z (rewrite cc in wc) (rewrite cd in wd) ltcxz ltzdx)
--             Refl
--             Refl
--             ltxy
--             ltyz

-- rewriteWRTB0
--   :  TotalOrd e
--   => {ll, rl : Tree e} -> {y : e} -> {c : Color}
--   -> (T node) === (T (N c ll y rl))
--   -> WRBT e (T node) (color (T node)) (value (T node)) n
--   -> WRBT e (T (N c ll y rl)) c (Just y) n
-- rewriteWRTB0 Refl wt = wt

-- rewriteWRTB1
--   :  TotalOrd e
--   => (x : e) -> (t : Tree e) -> {ll, rl : Tree e} -> {y : e} -> {c : Color}
--   -> insTree0 x t === (T (N c ll y rl))
--   -> WRBT e (insTree0 x t) (color (insTree0 x t)) (value (insTree0 x t)) n
--   -> WRBT e (insTree0 x t) (color (insTree0 x t)) (value (insTree0 x t)) n === WRBT e (T (N c ll y rl)) c (Just y) n
-- rewriteWRTB1 x t ixl wt = rewrite ixl in Refl

-- rewriteWRTB
--   :  TotalOrd e
--   => (x : e) -> (t : Tree e) -> {ll, rl : Tree e} -> {y : e} -> {c : Color}
--   -> insTree0 x t === (T (N c ll y rl))
--   -> WRBT e (insTree0 x t) (color (insTree0 x t)) (value (insTree0 x t)) n
--   -> WRBT e (T (N c ll y rl)) c (Just y) n
-- rewriteWRTB x E ixl wt = rewriteWRTB0 ixl wt
-- rewriteWRTB x (T (N R t w t1)) ixl wt with (compare x w)
--   _ | LT = rewriteWRTB0 ixl wt
--   _ | EQ = rewriteWRTB0 ixl wt
--   _ | GT = rewriteWRTB0 ixl wt
-- rewriteWRTB x (T (N B E w E)) ixl wt with (compare x w)
--   _ | LT = rewriteWRTB0 ixl wt
--   _ | EQ = rewriteWRTB0 ixl wt
--   _ | GT = rewriteWRTB0 ixl wt
-- rewriteWRTB x (T (N B E w E)) ixl wt with (compare x w)
--   _ | LT = rewriteWRTB0 ixl wt
--   _ | EQ = rewriteWRTB0 ixl wt
--   _ | GT = rewriteWRTB0 ixl wt
-- rewriteWRTB x (T (N B E w (T (N R E v E)))) ixl wt with (compare x w)
--   _ | LT = rewriteWRTB0 ixl wt
--   _ | EQ = rewriteWRTB0 ixl wt
--   _ | GT = rewriteWRTB0 ixl wt
-- rewriteWRTB x (T (N B E w (T (N R E v (T (N R t s t1)))))) ixl wt with (compare x w)
--   _ | LT = rewriteWRTB0 ixl wt
--   _ | EQ = rewriteWRTB0 ixl wt
--   _ | GT = rewriteWRTB0 ixl wt
-- rewriteWRTB x (T (N B E w (T (N R E v (T (N B t s r)))))) ixl wt with (compare x w)
--   _ | LT = rewriteWRTB0 ixl wt
--   _ | EQ = rewriteWRTB0 ixl wt
--   _ | GT = rewriteWRTB0 ixl wt
-- rewriteWRTB x (T (N B E w (T (N R (T (N R t s t2)) v t1)))) ixl wt with (compare x w)
--   _ | LT = rewriteWRTB0 ixl wt
--   _ | EQ = rewriteWRTB0 ixl wt
--   _ | GT = rewriteWRTB0 ixl wt
-- rewriteWRTB x (T (N B E w (T (N R (T (N B t s t2)) v E)))) ixl wt with (compare x w)
--   _ | LT = rewriteWRTB0 ixl wt
--   _ | EQ = rewriteWRTB0 ixl wt
--   _ | GT = rewriteWRTB0 ixl wt
-- rewriteWRTB x (T (N B E w (T (N R (T (N B t s t2)) v (T (N R t1 u t3)))))) ixl wt with (compare x w)
--   _ | LT = rewriteWRTB0 ixl wt
--   _ | EQ = rewriteWRTB0 ixl wt
--   _ | GT = rewriteWRTB0 ixl wt
-- rewriteWRTB x (T (N B E w (T (N R (T (N B t s t2)) v (T (N B t1 u t3)))))) ixl wt with (compare x w)
--   _ | LT = rewriteWRTB0 ixl wt
--   _ | EQ = rewriteWRTB0 ixl wt
--   _ | GT = rewriteWRTB0 ixl wt
-- rewriteWRTB x (T (N B E w (T (N B t v t1)))) ixl wt with (compare x w)
--   _ | LT = rewriteWRTB0 ixl wt
--   _ | EQ = rewriteWRTB0 ixl wt
--   _ | GT = rewriteWRTB0 ixl wt
-- rewriteWRTB x (T (N B (T (N R E v E)) w r)) ixl wt with (compare x w)
--   _ | LT = rewriteWRTB0 ixl wt
--   _ | EQ = rewriteWRTB0 ixl wt
--   _ | GT = rewriteWRTB0 ixl wt
-- rewriteWRTB x (T (N B (T (N R E v (T (N R t s t1)))) w r)) ixl wt with (compare x w)
--   _ | LT = rewriteWRTB0 ixl wt
--   _ | EQ = rewriteWRTB0 ixl wt
--   _ | GT = rewriteWRTB0 ixl wt
-- rewriteWRTB x (T (N B (T (N R E v (T (N B t s t1)))) w r)) ixl wt with (compare x w)
--   _ | LT = rewriteWRTB0 ixl wt
--   _ | EQ = rewriteWRTB0 ixl wt
--   _ | GT = rewriteWRTB0 ixl wt
-- rewriteWRTB x (T (N B (T (N R (T (N R t s t2)) v t1)) w r)) ixl wt with (compare x w)
--   _ | LT = rewriteWRTB0 ixl wt
--   _ | EQ = rewriteWRTB0 ixl wt
--   _ | GT = rewriteWRTB0 ixl wt
-- rewriteWRTB x (T (N B (T (N R (T (N B t s t2)) v E)) w r)) ixl wt with (compare x w)
--   _ | LT = rewriteWRTB0 ixl wt
--   _ | EQ = rewriteWRTB0 ixl wt
--   _ | GT = rewriteWRTB0 ixl wt
-- rewriteWRTB x (T (N B (T (N R (T (N B t s t2)) v (T (N R t1 u t3)))) w r)) ixl wt with (compare x w)
--   _ | LT = rewriteWRTB0 ixl wt
--   _ | EQ = rewriteWRTB0 ixl wt
--   _ | GT = rewriteWRTB0 ixl wt
-- rewriteWRTB x (T (N B (T (N R (T (N B t s t2)) v (T (N B t1 u t3)))) w r)) ixl wt with (compare x w)
--   _ | LT = rewriteWRTB0 ixl wt
--   _ | EQ = rewriteWRTB0 ixl wt
--   _ | GT = rewriteWRTB0 ixl wt
-- rewriteWRTB x (T (N B (T (N B t v t1)) w E)) ixl wt with (compare x w)
--   _ | LT = rewriteWRTB0 ixl wt
--   _ | EQ = rewriteWRTB0 ixl wt
--   _ | GT = rewriteWRTB0 ixl wt
-- rewriteWRTB x (T (N B (T (N B t v t1)) w (T (N R E s t3)))) ixl wt with (compare x w)
--   _ | LT = rewriteWRTB0 ixl wt
--   _ | EQ = rewriteWRTB0 ixl wt
--   _ | GT = rewriteWRTB0 ixl wt
-- rewriteWRTB x (T (N B (T (N B t v t1)) w (T (N R (T (N R t2 u t4)) s t3)))) ixl wt with (compare x w)
--   _ | LT = rewriteWRTB0 ixl wt
--   _ | EQ = rewriteWRTB0 ixl wt
--   _ | GT = rewriteWRTB0 ixl wt
-- rewriteWRTB x (T (N B (T (N B t v t1)) w (T (N R (T (N B t2 u t4)) s E)))) ixl wt with (compare x w)
--   _ | LT = rewriteWRTB0 ixl wt
--   _ | EQ = rewriteWRTB0 ixl wt
--   _ | GT = rewriteWRTB0 ixl wt
-- rewriteWRTB x (T (N B (T (N B t v t1)) w (T (N R (T (N B t2 u t4)) s (T (N R t3 x1 t5)))))) ixl wt with (compare x w)
--   _ | LT = rewriteWRTB0 ixl wt
--   _ | EQ = rewriteWRTB0 ixl wt
--   _ | GT = rewriteWRTB0 ixl wt
-- rewriteWRTB x (T (N B (T (N B t v t1)) w (T (N R (T (N B t2 u t4)) s (T (N B t3 x1 t5)))))) ixl wt with (compare x w)
--   _ | LT = rewriteWRTB0 ixl wt
--   _ | EQ = rewriteWRTB0 ixl wt
--   _ | GT = rewriteWRTB0 ixl wt
-- rewriteWRTB x (T (N B (T (N B t v t1)) w (T (N B t2 s t3)))) ixl wt with (compare x w)
--   _ | LT = rewriteWRTB0 ixl wt
--   _ | EQ = rewriteWRTB0 ixl wt
--   _ | GT = rewriteWRTB0 ixl wt

-- absurdInsTree0 : Ord e => (x : e) -> (t : Tree e) -> Not (insTree0 x t === E)
-- absurdInsTree0 x E t' = absurdTree t'
-- absurdInsTree0 x (T (N y t z t1)) t' with (compare x z) proof xz
--   _ | LT = absurdTree t'
--   _ | EQ = absurdTree t'
--   _ | GT = absurdTree t'

-- insTreeEmpty : TotalOrd e => (x : e) -> (t : Tree e) -> insTree0 x t === T (N R E y E) -> x === y
-- insTreeEmpty y E     Refl = Refl
-- insTreeEmpty x (T (N R t w t1)) ixl with (compare x w)
--   _ | LT = ?ite_2a -- insTree can not be empty
--   _ | EQ = ?ite_2b
--   _ | GT = ?ite_2c -- insTree can not be empty
-- insTreeEmpty x (T (N B t w t1)) ixl with (compare x w)
--   _ | LT = ?ite_2d
--   _ | EQ = ?ite_2e
--   _ | GT = ?ite_2f

insertWT0
  :  TotalOrd e => {x : e} -> {t : Tree e}
  -> (n : Nat ** WRBT e t B v n)
  -> (m : Nat ** WRBT e (insert0 x t) B (value (insert0 x t)) m)
insertWT0 ((0 ** WE)) = (1 ** WBN x WE WE LeafLeft LeafRight)

insertWT0 (((S 0) ** (WBN y
                        WE
                        WE
                        lx
                        xr))) with (compare x y) proof xy
  _ | LT = (1 ** WBN y (WRN x WE WE Refl Refl LeafLeft LeafRight) WE (NodeLT xy) LeafRight)
  _ | EQ = (1 ** WBN y WE WE lx xr)
  _ | GT = (1 ** WBN y WE (WRN x WE WE Refl Refl LeafLeft LeafRight) lx (NodeLT (compareGtLt _ _ xy)))

-- WRBT e (T (N B E y (T (N R E x E)))) B (Just y) 2

insertWT0 (((S 0) ** (WBN y
                        WE
                        (WRN z WE WE cl cr w s)
                        lx
                        xr))) = ?x1_10

insertWT0 (((S (S 0)) ** (WBN y (WBN z WE w s u) (WBN x1 wl wr lx1 xr1) lx xr))) = ?x1_12

insertWT0 (((S (S 0)) ** (WBN y (WBN z WE w s u) (WRN x1 wl wr cl cr lx1 xr1) lx xr))) = ?x1_13

insertWT0 (((S (S (S 0))) ** (WBN y (WBN z  (WBN x1 WE WE lx1 xr1)  (WBN w WE WE t1 u1) s u) (WBN y1 (WBN x2 WE WE lx2 xr2) (WBN y2 WE WE z2 w2) z1 w1) lx xr))) with (compare x y) proof xy
  _ | LT with (compare x z) proof xz
    _ | LT with (compare x x1) proof xx1
      _ | LT = ?w1_15aaa
      _ | EQ = ?w1_15aab
      _ | GT = ?w1_15aac
    _ | EQ = ?w1_15ab
    _ | GT = ?w1_15ac
  _ | EQ = ?w1_15b
  _ | GT = ?w1_15c

insertWT0 (((S (S (S 0))) ** (WBN y (WBN z  (WBN x1 WE WE lx1 xr1)  (WBN w WE WE t1 u1) s u) (WBN y1 (WBN x2 WE WE lx2 xr2) (WBN y2 WE (WRN v1 wl wr cl cr s1 v2) z2 w2) z1 w1) lx xr))) = ?w1_16
insertWT0 (((S (S (S 0))) ** (WBN y (WBN z  (WBN x1 WE WE lx1 xr1)  (WBN w WE WE t1 u1) s u) (WBN y1 (WBN x2 WE WE lx2 xr2) (WBN y2 (WRN v1 wl wr1 cl cr s1 v2) wr z2 w2) z1 w1) lx xr))) = ?w1_14
insertWT0 (((S (S (S 0))) ** (WBN y (WBN z  (WBN x1 WE WE lx1 xr1)  (WBN w WE WE t1 u1) s u) (WBN y1 (WBN x2 WE (WRN v1 wl wr1 cl cr s1 v2) lx2 xr2) (WBN y2 wl2 wr z2 w2) z1 w1) lx xr))) = ?w1_12

insertWT0 (((S (S (S 0))) ** (WBN y (WBN z  (WBN x1 WE WE lx1 xr1)  (WBN w WE WE t1 u1) s u) (WBN y1 (WBN x2 (WRN v1 wl wr1 cl cr s1 v2) wr2 lx2 xr2) (WBN y2 wl2 wr z2 w2) z1 w1) lx xr))) = ?w1_10
insertWT0 (((S (S (S 0))) ** (WBN y (WBN z  (WBN x1 WE WE lx1 xr1)  (WBN w WE (WRN v1 wl wr1 cl cr s1 v2) t1 u1) s u) (WBN y1 (WBN x2 wl1 wr2 lx2 xr2) (WBN y2 wl2 wr z2 w2) z1 w1) lx xr))) = ?w1_8
insertWT0 (((S (S (S 0))) ** (WBN y (WBN z  (WBN x1 WE WE lx1 xr1)  (WBN w (WRN v1 wl wr1 cl cr v2 s2) s1 t1 u1) s u) (WBN y1 (WBN x2 wl1 wr2 lx2 xr2) (WBN y2 wl2 wr z2 w2) z1 w1) lx xr))) = ?w1_6
insertWT0 (((S (S (S 0))) ** (WBN y (WBN z  (WBN x1 WE (WRN v2 wl wr1 cl cr s2 t2) lx1 xr1)  (WBN w v1 s1 t1 u1) s u) (WBN y1 (WBN x2 wl1 wr2 lx2 xr2) (WBN y2 wl2 wr z2 w2) z1 w1) lx xr))) = ?w1_4

insertWT0 (((S (S (S (S n)))) ** (WBN y (WBN z (WBN x1 (WBN v2 wl s2 t2 u2) wr1 lx1 xr1) (WBN w v1 s1 t1 u1) s u) (WBN y1 (WBN x2 (WBN x3 wl1 wr3 lx3 xr3) (WBN y3 wl3 wr2 z3 w3) lx2 xr2) (WBN y2 (WBN v3 wl2 s3 t3 u3) (WBN x4 wl4 wr lx4 xr4) z2 w2) z1 w1) lx xr)))
  with (compare x y) proof xy
    _ | LT with (compare x z) proof xz
      _ | LT with (compare x x1) proof xx1
        _ | LT with (compare x v2) proof xv2
          _ | LT = ?w1_16aaaa
          _ | EQ = ?w1_16aaab
          _ | GT = ?w1_16aaac
        _ | EQ = ?w1_16aab
        _ | GT = ?w1_16aac
      _ | EQ = ?w1_16ab
      _ | GT = ?w1_16ac
    _ | EQ = ?w1_16b
    _ | GT = ?w1_16c


insertWT0 (((S (S (S (S n)))) ** (WBN y (WBN z (WBN x1 (WBN v2 wl s2 t2 u2) wr1 lx1 xr1) (WBN w v1 s1 t1 u1) s u) (WBN y1 (WBN x2 (WBN x3 wl1 wr3 lx3 xr3) (WBN y3 wl3 wr2 z3 w3) lx2 xr2) (WBN y2 (WBN v3 wl2 s3 t3 u3) (WRN x4 wl4 wr cl cr lx4 xr4) z2 w2) z1 w1) lx xr))) = ?w1_17

insertWT0 (((S (S (S (S n)))) ** (WBN y (WBN z (WBN x1 (WBN v2 wl s2 t2 u2) wr1 lx1 xr1) (WBN w v1 s1 t1 u1) s u) (WBN y1 (WBN x2 (WBN x3 wl1 wr3 lx3 xr3) (WBN y3 wl3 wr2 z3 w3) lx2 xr2) (WBN y2 (WRN v3 wl2 s3 cl cr t3 u3) wr z2 w2) z1 w1) lx xr))) = ?w1_13

insertWT0 (((S (S (S (S n)))) ** (WBN y (WBN z (WBN x1 (WBN v2 wl s2 t2 u2) wr1 lx1 xr1) (WBN w v1 s1 t1 u1) s u) (WBN y1 (WBN x2 (WBN x3 wl1 wr3 lx3 xr3) (WRN y3 wl3 wr2 cl cr z3 w3) lx2 xr2) (WBN y2 wl2 wr z2 w2) z1 w1) lx xr))) = ?w1_9
insertWT0 (((S (S (S (S n)))) ** (WBN y (WBN z (WBN x1 (WBN v2 wl s2 t2 u2) wr1 lx1 xr1) (WBN w v1 s1 t1 u1) s u) (WBN y1 (WBN x2 (WRN x3 wl1 wr3 cl cr lx3 xr3) wr2 lx2 xr2) (WBN y2 wl2 wr z2 w2) z1 w1) lx xr))) = ?w1_5

insertWT0 (((S (S (S n))) ** (WBN y (WBN z  (WBN x1 (WRN v2 wl s2 cl cr t2 u2) wr1 lx1 xr1)  (WBN w v1 s1 t1 u1) s u) (WBN y1 (WBN x2 wl1 wr2 lx2 xr2) (WBN y2 wl2 wr z2 w2) z1 w1) lx xr))) = ?w1_2

-- with (compare x y) proof xy
--   _ | LT with (compare x z) proof xz
--     _ | LT with (compare x x1) proof xx1
--       _ | LT = ?x1_20aa
--       _ | EQ = ?x1_20ab
--       _ | GT = ?x1_20ac
--     _ | EQ = ?x1_20b
--     _ | GT = ?x1_20d
--   _ | EQ = (S (S (S n)) ** WBN y (WBN z (WBN x1 wl wr1 lx1 xr1) (WBN w v1 s1 t1 u1) s u) (WBN y1 (WBN x2 wl1 wr2 lx2 xr2) (WBN y2 wl2 wr z2 w2) z1 w1) lx xr)
--   _ | GT = ?x1_20c

insertWT0 (((S (S (S n))) ** (WBN y (WBN z (WBN x1 wl wr1 lx1 xr1) (WBN w v1 s1 t1 u1) s u) (WBN y1 (WBN x2 wl1 wr2 lx2 xr2) (WRN y2 wl2 wr cl cr z2 w2) z1 w1) lx xr))) = ?x1_21

insertWT0 (((S (S (S n))) ** (WBN y (WBN z (WBN x1 wl wr1 lx1 xr1) (WBN w v1 s1 t1 u1) s u) (WBN y1 (WRN x2 wl1 wr2 cl cr lx2 xr2) (WBN y2 wl2 wr z2 w2) z1 w1) lx xr))) = ?x1_22
insertWT0 (((S (S (S n))) ** (WBN y (WBN z (WBN x1 wl wr1 lx1 xr1) (WBN w v1 s1 t1 u1) s u) (WBN y1 (WRN x2 wl1 wr2 cl cr lx2 xr2) (WRN y2 wl2 wr prf cr1 z2 w2) z1 w1) lx xr))) = ?x1_23

insertWT0 (((S (S (S n))) ** (WBN y (WBN z (WBN x1 wl wr1 lx1 xr1) (WRN w v1 s1 cl cr t1 u1) s u) (WBN y1 (WBN x2 wl1 wr2 lx2 xr2) (WBN y2 wl2 wr z2 w2) z1 w1) lx xr))) = ?x1_24
insertWT0 (((S (S (S n))) ** (WBN y (WBN z (WBN x1 wl wr1 lx1 xr1) (WRN w v1 s1 cl cr t1 u1) s u) (WBN y1 (WBN x2 wl1 wr2 lx2 xr2) (WRN y2 wl2 wr prf cr1 z2 w2) z1 w1) lx xr))) = ?x1_25
insertWT0 (((S (S (S n))) ** (WBN y (WBN z (WBN x1 wl wr1 lx1 xr1) (WRN w v1 s1 cl cr t1 u1) s u) (WBN y1 (WRN x2 wl1 wr2 prf cr1 lx2 xr2) (WBN y2 wl2 wr z2 w2) z1 w1) lx xr))) = ?x1_26
insertWT0 (((S (S (S n))) ** (WBN y (WBN z (WBN x1 wl wr1 lx1 xr1) (WRN w v1 s1 cl cr t1 u1) s u) (WBN y1 (WRN x2 wl1 wr2 prf cr1 lx2 xr2) (WRN y2 wl2 wr cl1 prf1 z2 w2) z1 w1) lx xr))) = ?x1_27

insertWT0 (((S (S (S n))) ** (WBN y (WBN z (WBN x1 wl wr1 lx1 xr1) (WBN w v1 s1 t1 u1) s u) (WRN y1 (WBN x2 wl1 wr2 lx2 xr2) (WBN y2 wl2 wr z2 w2) cl cr z1 w1) lx xr))) = ?x1_19
insertWT0 (((S (S (S n))) ** (WBN y (WBN z (WBN x1 wl wr1 lx1 xr1) (WRN w v1 s1 prf cr1 t1 u1) s u) (WRN y1 (WBN x2 wl1 wr2 lx2 xr2) (WBN y2 wl2 wr z2 w2) cl cr z1 w1) lx xr))) = ?x1_28

insertWT0 (((S (S 0)) ** (WBN y (WBN z (WRN x1 wl wr1 cl cr lx1 xr1) WE s u) (WBN w WE WE y1 z1) lx xr))) = ?x1_31
insertWT0 (((S (S 0)) ** (WBN y (WBN z (WRN x1 wl wr1 cl cr lx1 xr1) WE s u) (WBN w WE (WRN w1 wl1 wr prf cr1 v1 s1) y1 z1) lx xr))) = ?x1_32

insertWT0 (((S (S 0)) ** (WBN y (WBN z (WRN x1 wl wr1 cl cr lx1 xr1) WE s u) (WBN w (WRN w1 wl1 v1 prf cr1 s1 t1) WE y1 z1) lx xr))) = ?x1_33
insertWT0 (((S (S 0)) ** (WBN y (WBN z (WRN x1 wl wr1 cl cr lx1 xr1) WE s u) (WBN w (WRN w1 wl1 v1 prf cr1 s1 t1) (WRN u1 wl2 wr cl1 prf1 lx2 xr2) y1 z1) lx xr))) = ?x1_34

insertWT0 (((S (S 0)) ** (WBN y (WBN z (WRN x1 wl wr1 cl cr lx1 xr1) WE s u) (WRN w (WBN w1 wl1 v1 s1 t1) (WBN u1 wl2 wr lx2 xr2) prf cr1 y1 z1) lx xr))) = ?x1_30

insertWT0 (((S (S (S 0))) ** (WBN y (WBN z (WRN x1 wl wr1 cl cr lx1 xr1) (WBN w WE y1 z1 w1) s u) (WBN v1 wl1 wr s1 t1) lx xr))) = ?x1_35
insertWT0 (((S (S (S 0))) ** (WBN y (WBN z (WRN x1 wl wr1 cl cr lx1 xr1) (WBN w WE y1 z1 w1) s u) (WRN v1 wl1 wr prf cr1 s1 t1) lx xr))) = ?x1_36
insertWT0 (((S (S (S (S n)))) ** (WBN y (WBN z (WRN x1 wl wr1 cl cr lx1 xr1) (WBN w (WBN v1 wl1 s1 t1 u1) y1 z1 w1) s u) (WBN x2 wl2 wr lx2 xr2) lx xr))) = ?x1_37
insertWT0 (((S (S (S (S n)))) ** (WBN y (WBN z (WRN x1 wl wr1 cl cr lx1 xr1) (WBN w (WBN v1 wl1 s1 t1 u1) y1 z1 w1) s u) (WRN x2 wl2 wr prf cr1 lx2 xr2) lx xr))) = ?x1_38

insertWT0 (((S (S (S n))) ** (WBN y (WBN z (WRN x1 wl wr1 cl cr lx1 xr1) (WBN w (WRN v1 wl1 s1 prf cr1 t1 u1) y1 z1 w1) s u) (WBN x2 wl2 wr lx2 xr2) lx xr))) = ?x1_39
insertWT0 (((S (S (S n))) ** (WBN y (WBN z (WRN x1 wl wr1 cl cr lx1 xr1) (WBN w (WRN v1 wl1 s1 prf cr1 t1 u1) y1 z1 w1) s u) (WRN x2 wl2 wr cl1 prf1 lx2 xr2) lx xr))) = ?x1_40

insertWT0 (((S (S 0)) ** (WBN y (WBN z (WRN x1 wl wr1 cl cr lx1 xr1) (WRN w wl1 y1 prf cr1 z1 w1) s u) (WBN v1 WE WE t1 u1) lx xr))) = ?x1_43
insertWT0 (((S (S 0)) ** (WBN y (WBN z (WRN x1 wl wr1 cl cr lx1 xr1) (WRN w wl1 y1 prf cr1 z1 w1) s u) (WBN v1 WE (WRN s1 wl2 wr cl1 prf1 lx2 xr2) t1 u1) lx xr))) = ?x1_44

insertWT0 (((S (S (S n))) ** (WBN y (WBN z (WRN x1 wl wr1 cl cr lx1 xr1) (WRN w wl1 y1 prf cr1 z1 w1) s u) (WBN v1 (WBN s1 wl2 wr2 lx2 xr2) (WBN x2 y2 wr z2 w2) t1 u1) lx xr))) = ?x1_45
insertWT0 (((S (S (S n))) ** (WBN y (WBN z (WRN x1 wl wr1 cl cr lx1 xr1) (WRN w wl1 y1 prf cr1 z1 w1) s u) (WBN v1 (WBN s1 wl2 wr2 lx2 xr2) (WRN x2 y2 wr cl1 prf1 z2 w2) t1 u1) lx xr))) = ?x1_46

insertWT0 (((S (S 0)) ** (WBN y (WBN z (WRN x1 wl wr1 cl cr lx1 xr1) (WRN w wl1 y1 prf cr1 z1 w1) s u) (WBN v1 (WRN s1 wl2 wr2 cl1 prf1 lx2 xr2) WE t1 u1) lx xr))) = ?x1_47
insertWT0 (((S (S (S n))) ** (WBN y (WBN z (WRN x1 wl wr1 cl cr lx1 xr1) (WRN w wl1 y1 prf cr1 z1 w1) s u) (WBN v1 (WRN s1 wl2 wr2 cl1 prf1 lx2 xr2) (WBN x2 y2 wr z2 w2) t1 u1) lx xr))) = ?x1_48
insertWT0 (((S (S n)) ** (WBN y (WBN z (WRN x1 wl wr1 cl cr lx1 xr1) (WRN w wl1 y1 prf cr1 z1 w1) s u) (WBN v1 (WRN s1 wl2 wr2 cl1 prf1 lx2 xr2) (WRN x2 y2 wr cl2 cr2 z2 w2) t1 u1) lx xr))) = ?x1_49

insertWT0 (((S (S n)) ** (WBN y (WBN z (WRN x1 wl wr1 cl cr lx1 xr1) (WRN w wl1 y1 prf cr1 z1 w1) s u) (WRN v1 s1 wr cl1 prf1 t1 u1) lx xr))) = ?x1_18

insertWT0 (((S k) ** (WBN y (WRN z wl w cl cr s u) wr lx xr))) = ?x1_6

insertWT0 _ = ?insertWT0_missing_case_1

-- insertWT
--   :  TotalOrd e => (x : e) -> (t : Tree e)
--   -> (n : Nat ** WRBT e t B v n)
--   -> (m : Nat ** WRBT e (insert0 x t) B (value (insert0 x t)) m)
-- insertWT x E wt = ?h1_0
-- insertWT x (T (N R t z t1)) wt = ?impossible1
-- insertWT x (T (N B E z E)) wt = ?h1_7
-- insertWT x (T (N B E z (T (N R E w E)))) wt = ?h1_18
-- insertWT x (T (N B E z (T (N R E w (T (N R t s t1)))))) wt = ?impossible4 -- red red
-- insertWT x (T (N B E z (T (N R E w (T (N B t s t1)))))) wt = ?impossible5 -- different black height
-- insertWT x (T (N B E z (T (N R (T (N R t s t2)) w t1)))) wt = ?impossible6 -- red red
-- insertWT x (T (N B E z (T (N R (T (N B t s t2)) w t1)))) wt = ?impossible7 -- different black height
-- insertWT x (T (N B E z (T (N B t w t1)))) wt = ?impossible8 -- different black height
-- insertWT x (T (N B (T (N R E w E)) z E)) wt = ?h1_17
-- insertWT x (T (N B (T (N R E w (T (N R t s t1)))) z E)) wt = ?impossible11 -- red red
-- insertWT x (T (N B (T (N R E w (T (N B t s t1)))) z E)) wt = ?impossible12 -- different black height
-- insertWT x (T (N B (T (N R (T (N R t s t2)) w t1)) z E)) wt = ?impossible9 -- red red
-- insertWT x (T (N B (T (N R (T (N B t s t2)) w t1)) z E)) wt = ?impossible10 -- different black height
-- insertWT x (T (N B (T (N B t w t1)) z E)) wt = ?h1_15
-- insertWT x (T (N B (T (N R E u t3)) z (T (N w t s t1)))) wt = ?h1_19
-- insertWT x (T (N B (T (N R (T (N R t2 x1 t4)) u t3)) z (T (N w t s t1)))) wt = ?impossible2
-- insertWT x (T (N B (T (N R (T (N B t2 x1 t4)) u E)) z (T (N w t s t1)))) wt = ?h1_26
-- insertWT x (T (N B (T (N R (T (N B t2 x1 t4)) u (T (N R t3 y1 t5)))) z (T (N w t s t1)))) wt = ?impossible3
-- insertWT x (T (N B (T (N R (T (N B t2 x1 t4)) u (T (N B t3 y1 t5)))) z (T (N w t s t1)))) wt = ?h1_30
-- insertWT x (T (N B (T (N B E u t3)) z (T (N w t s t1)))) wt = ?h1_21
-- insertWT x (T (N B (T (N B (T y) u t3)) z (T (N w t s t1)))) wt = ?h1_22

-- insTreeWT
--   : TotalOrd e => (x : e) -> (t : Tree e)
--   -> (n : Nat ** WRBT e t c v n)
--   -> (m : Nat ** WRBT e (insTree0 x t) (color (insTree0 x t)) (value (insTree0 x t)) m)
-- insTreeWT x E (0 ** WE) = (0 ** WRN x WE WE Refl Refl LeafLeft LeafRight)
-- insTreeWT x (T (N B l z r)) (S n ** WBN z wl wr lx xr) with (compare x z) proof xz
--   -- _ | LT with (insTreeWT x l wl) proof ixl
--   --   _ | wt with (insTree0 x l)
--   --     _ | tr = ?w2
--   _ | LT with (insTree0 x l) proof ixl
--     -- Impossible; insTree can not create empty tree
--     _ | E = case (insTreeWT x l (n ** wl)) of
--           pat => void (absurdInsTree0 _ _ ixl)
--     _ | T (N R E xi E) with (insTreeWT x l (n ** wl)) proof ixl
--       _ | wt with (r)
--         _ | E
--             = (1 ** WBN z
--                       (WRN xi WE WE Refl Refl LeafLeft LeafRight)
--                       WE
--                       (NodeLT (case insTreeEmpty _ _ ixl of
--                                 pat => rewrite (sym pat) in xz))
--                       xr)
--         _ | T (N R E rx E)
--             = (1 ** WBN z
--                       (WRN xi WE WE Refl Refl LeafLeft LeafRight)
--                       (WRN rx WE WE Refl Refl LeafLeft LeafRight)
--                       (NodeLT (case insTreeEmpty _ _ ixl of
--                                 pat => rewrite (sym pat) in xz))
--                       xr)
--         _ | T (N R E rx (T (N B rrl rrx rrr)))
--             = (1 ** ?w1a)
--         _ | T (N R E rx (T (N R rrl rrx rrr))) = ?w1aac
--         _ | T (N R (T (N B rrl rrx rrr)) rx rr) = ?w1aaaa
--         _ | T (N R (T (N R rrl rrx rrr)) rx rr) = ?w1aaba
--         _ | T (N B rl rx rr) = ?w1ab
--     _ | T (N R E xi (T (N R rl rx rr))) with (insTreeWT x l (n ** wl)) proof ixl
--       _ | wt = case (rewriteWRTB _ _ ixl (snd wt)) of
--             wt1 => ?isThisRight
--     _ | T (N R E xi (T (N B rl rx rr))) = ?w1g
--     _ | T (N R (T (N R lli lxi lri)) xi ri) = ?w1b
--     _ | T (N R (T (N B lli lxi lri)) xi ri) = ?w1e
--     _ | T (N B li xi ri) = ?w1c
--   -- _ | LT with (insTree0 x l) proof ixl
--   --   _ | E = void (absurdInsTree0 _ _ ixl)
--   --   _ | T (N R E xi E) = ?w1a
--   --   _ | T (N R E xi (T (N R rl rx rr))) = ?w1f
--   --   _ | T (N R E xi (T (N B rl rx rr))) = ?w1g
--   --   _ | T (N R (T (N R lli lxi lri)) xi ri) =
--   --       (?w1c_0 ** (?w1c_2 **
--   --         WRN xi
--   --           (WBN lxi ?w1c_12 ?w1c_13 ?w1c_14 ?w1c_15)
--   --           (WBN z ?w1c_16 wr ?w1c_18 xr)
--   --           Refl
--   --           Refl
--   --           ?w1c_9
--   --           ?w1c_10))
--   --   _ | T (N R (T (N B lli lxi lri)) xi ri) = ?w1e
--   --   _ | T (N B li xi ri) = ?w1b
--   _ | EQ = (S n ** WBN z wl wr lx xr)
--   _ | GT = ?w1d
-- insTreeWT x (T (N R l z r)) (n ** WRN z wl wr cl cr lx xr) = ?insTreeWT_rhs_2

-- -- balanceTreeCase2
-- --   : TotalOrd e
-- --   => (a,b,c,d : Tree e)
-- --   -> WRBT e a B (value a) n
-- --   -> WRBT e b B (value b) n
-- --   -> WRBT e c B (value c) n
-- --   -> WRBT e d B (value d) n
-- --   -> (x,y,z : e)
-- --   -> LessThan (value a) (Just x)
-- --   -> LessThan (Just x) (value b)
-- --   -> LessThan (Just x) (Just y)
-- --   -> LessThan (Just y) (value c)
-- --   -> LessThan (value c) (Just z)
-- --   -> LessThan (Just y) (Just z)
-- --   -> LessThan (Just z) (value d)
-- --   -> WRBT e (T (balance (N B (T (N R a x (T (N R b y c)))) z d))) R (Just y) (S n)
-- -- balanceTreeCase2 a b c d wa wb wc wd x y z ltaxx ltxbx ltxy ltycx ltcxz ltyz ltzdx
-- --   = ?r1 -- WRN y (WBN x wa wb ltaxx ltxbx) (WBN z wc wd ltcxz ltzdx) Refl Refl ltxy ltyz