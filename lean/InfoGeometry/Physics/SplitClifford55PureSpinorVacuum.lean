import Mathlib.LinearAlgebra.CliffordAlgebra.Contraction
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
import Mathlib.LinearAlgebra.QuadraticForm.Basic

/-!
# Isotropic Clifford restrictions and exterior creation

This module keeps two carriers distinct. Restricting a quadratic form to an
isotropic subspace gives the zero quadratic form, whose Clifford algebra is
the exterior algebra. This identifies the restricted Clifford algebra, not
the ambient Clifford algebra, with the exterior algebra. On that
exterior-algebra carrier, creation by a generator squares to zero. No
dimension, signature, spacetime-emergence, or spin-statistics theorem is
asserted here.
-/

namespace InfoGeometry.Physics.PureSpinor

variable {R V W W_star : Type*} [CommRing R]
variable [AddCommGroup V] [Module R V]
variable [AddCommGroup W] [Module R W]
variable [AddCommGroup W_star] [Module R W_star]

variable (Q : QuadraticForm R V)
variable (W_inject : W →ₗ[R] V)
variable (W_star_inject : W_star →ₗ[R] V)

variable (h_isotropic_W : Q.comp W_inject = 0)
variable (h_isotropic_W_star : Q.comp W_star_inject = 0)

/-- The Clifford algebra of the restriction of `Q` to the isotropic image of
`W_inject` is the exterior algebra of `W`. This is an equivalence for the
restricted quadratic form, not an equivalence from the ambient
`CliffordAlgebra Q`. -/
noncomputable def isotropicCliffordToExterior :
    CliffordAlgebra (Q.comp W_inject) ≃ₐ[R] ExteriorAlgebra R W := by
  rw [h_isotropic_W]

/-- The unit element of the exterior algebra, used as an algebraic vacuum
vector in this finite carrier. -/
noncomputable def pureSpinorVacuum : ExteriorAlgebra R W := 1

/-- Creation by `w` is left multiplication by its exterior generator. -/
noncomputable def creationOperator (w : W) : Module.End R (ExteriorAlgebra R W) :=
  LinearMap.mulLeft R (ExteriorAlgebra.ι R w)

/-- Repeated creation by the same exterior generator vanishes on every state.
This is the alternating-product identity `ι(w) * ι(w) = 0`. -/
theorem pureSpinor_pauli_exclusion (w : W) (state : ExteriorAlgebra R W) :
    creationOperator w (creationOperator w state) = 0 := by
  dsimp [creationOperator]
  rw [← mul_assoc, ExteriorAlgebra.ι_sq_zero, zero_mul]

/-- The annihilation-side isotropic restriction has the same exterior-algebra
description. This still concerns the restricted quadratic form on `W_star`,
not the ambient Clifford algebra. -/
noncomputable def isotropicCliffordToExterior_star :
    CliffordAlgebra (Q.comp W_star_inject) ≃ₐ[R] ExteriorAlgebra R W_star := by
  rw [h_isotropic_W_star]

end InfoGeometry.Physics.PureSpinor
