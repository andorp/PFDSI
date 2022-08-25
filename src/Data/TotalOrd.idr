module Data.TotalOrd

||| Definition of total order, based on the Ord instance
||| rather than the LTE relation.
public export
interface Ord e => TotalOrd e where
  compareEq    : (x    : e) -> compare x x === EQ
  compareXY    : (x, y : e) -> compare x y === EQ -> x === y
  compareLtGt  : (x, y : e) -> compare x y === LT -> compare y x === GT
  compareGtLt  : (x, y : e) -> compare x y === GT -> compare y x === LT
  compareTrans : (x, y, z : e) -> compare x y === LT -> compare y z === LT -> compare x z === LT

export
ltNotEq : {o : Ordering} -> o === LT -> Not (o === EQ)
ltNotEq Refl prf1 impossible

export
eqNotLt : {o : Ordering} -> o === EQ -> Not (o === LT)
eqNotLt Refl prf1 impossible

export
gtNotLt : {o : Ordering} -> o === GT -> Not (o === LT)
gtNotLt Refl prf1 impossible
