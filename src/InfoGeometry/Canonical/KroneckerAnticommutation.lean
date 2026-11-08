import Mathlib.LinearAlgebra.Matrix.Kronecker
import InfoGeometry.Algebra.FiniteSpinAlgebra

set_option autoImplicit false

/-!
# Anticommutation transport through tensor products

This is the reusable algebraic step needed by the finite multi-site
Jordan--Wigner proof.  It separates the sign from the first tensor factor
and the commuting multiplication in the second factor.
-/

namespace InfoGeometry.Canonical.KroneckerAnticommutation

open scoped Kronecker
open Matrix

theorem mul_kronecker_anticomm_of_left_anticomm_of_right_comm
    {m p R : Type*} [Fintype m] [Fintype p] [CommRing R]
    (A C : Matrix m m R) (B D : Matrix p p R)
    (hAC : A * C = -(C * A))
    (hBD : B * D = D * B) :
    (A ⊗ₖ B) * (C ⊗ₖ D) + (C ⊗ₖ D) * (A ⊗ₖ B) = 0 := by
  rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, hAC, hBD]
  ext i j
  simp [Matrix.kroneckerMap_apply, Matrix.neg_apply]

end InfoGeometry.Canonical.KroneckerAnticommutation
