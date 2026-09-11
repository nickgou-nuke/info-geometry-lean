import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic

open Matrix

namespace InfoGeometry.OperatorAlgebra

/--
The two-by-two trace identity.

For any `2 × 2` matrix `A` and any `2 × 2` matrix `B` of determinant `1`,
`tr(A) tr(B) = tr(AB) + tr(AB⁻¹)`.  The determinant hypothesis is needed only
for `B`, since the inverse in the identity is `B⁻¹`.
-/
theorem sl2c_trace_identity {R : Type*} [CommRing R]
    (A B : Matrix (Fin 2) (Fin 2) R) (hB : B.det = 1) :
    A.trace * B.trace = (A * B).trace + (A * B⁻¹).trace := by
  have hBunit : IsUnit B.det := by
    rw [hB]
    exact isUnit_one
  rw [Matrix.nonsing_inv_apply B hBunit]
  simp [Matrix.adjugate_fin_two, Matrix.trace, Matrix.mul_apply, Fin.sum_univ_two, hB]
  ring

end InfoGeometry.OperatorAlgebra
