module Data.Cert

public export
data IsNo : (Dec a) -> Type where
  ItIsNo : IsNo (No no)

public export
absurdIsNo : IsNo (Yes ok) -> Void
absurdIsNo x impossible

public export
data IsYes : (Dec a) -> Type where
  ItIsYes : IsYes (Yes yes)

public export
absurdIsYes : IsYes (No no) -> Void
absurdIsYes x impossible

public export
data Tri : a -> b -> c -> Type where
  C1 : a -> Tri a b c
  C2 : b -> Tri a b c
  C3 : c -> Tri a b c
