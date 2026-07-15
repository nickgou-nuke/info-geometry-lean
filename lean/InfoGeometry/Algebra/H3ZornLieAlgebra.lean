import Mathlib
import Mathlib.Algebra.Lie.Subalgebra
import InfoGeometry.Algebra.QuadraticJordanH3Zorn

namespace InfoGeometry.Algebra.H3Zorn

variable (R : Type*) [CommRing R]

/-- The derivations of the exceptional Jordan algebra H₃(𝕆_s, -) form a Lie subalgebra 
of the endomorphism algebra. -/
def derivationLieSubalgebra : LieSubalgebra R (Module.End R (H3Zorn R)) where
  carrier := { f | ∃ D : Derivation R, f = D.toLinearMap }
  zero_mem' := sorry
  add_mem' := sorry
  smul_mem' := sorry
  lie_mem' := sorry

end InfoGeometry.Algebra.H3Zorn
