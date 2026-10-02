import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
import InfoGeometry.Clifford.Cl55BivectorVectorRepresentation

variable (R V : Type*) [CommRing R] [AddCommGroup V] [Module R V]

@[ext]
structure DerivPair where
  fst : ExteriorAlgebra R V
  snd : ExteriorAlgebra R V

namespace DerivPair

instance : Add (DerivPair R V) where
  add x y := ⟨x.fst + y.fst, x.snd + y.snd⟩

instance : Mul (DerivPair R V) where
  mul x y := ⟨x.fst * y.fst, x.fst * y.snd + x.snd * y.fst⟩

instance : Zero (DerivPair R V) where
  zero := ⟨0, 0⟩

instance : One (DerivPair R V) where
  one := ⟨1, 0⟩

instance : SMul R (DerivPair R V) where
  smul r x := ⟨r • x.fst, r • x.snd⟩

-- prove it's an R-algebra...
end DerivPair
