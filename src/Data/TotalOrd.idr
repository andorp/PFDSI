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

||| Helper function, if o is LT then it can not be EQ
export
ltNotEq : {o : Ordering} -> o === LT -> Not (o === EQ)
ltNotEq Refl prf1 impossible

||| Helper function, if o is EQ then it can not be LT
export
eqNotLt : {o : Ordering} -> o === EQ -> Not (o === LT)
eqNotLt Refl prf1 impossible

||| Helper function, if o is GT then it can not be LT
export
gtNotLt : {o : Ordering} -> o === GT -> Not (o === LT)
gtNotLt Refl prf1 impossible

||| Helper function, if o is LT then it can not be GT
export
ltNotGt : {o : Ordering} -> (o === LT) -> Not (o === GT)
ltNotGt Refl prf1 impossible  

||| Helper function, if o is GT then it can not be EQ
export
gtNotEq : {o : Ordering} -> (o === GT) -> Not (o === EQ)
gtNotEq Refl prf1 impossible
