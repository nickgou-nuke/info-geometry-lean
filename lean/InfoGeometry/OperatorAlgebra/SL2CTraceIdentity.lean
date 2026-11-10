import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic

open Matrix

namespace InfoGeometry.OperatorAlgebra

/-- Explicit `2 × 2` adjugate matrix `!![B 1 1, -B 0 1; -B 1 0, B 0 0]` over any ring `[Ring R]`. -/
def adjugate2 {R : Type*} [Ring R] (B : Matrix (Fin 2) (Fin 2) R) : Matrix (Fin 2) (Fin 2) R :=
  !![B 1 1, -B 0 1; -B 1 0, B 0 0]

/-- **Universal Non-Commutative `2 × 2` Trace–Adjugate Identity (`[Ring R]`):**
Over any associative (not necessarily commutative) ring `R` and for any `2 × 2` matrices
`A, B : Matrix (Fin 2) (Fin 2) R`, the off-diagonal terms in `tr(A B)` and `tr(A · adj(B))`
cancel in exact factor order, yielding `tr(A) * tr(B) = tr(A B) + tr(A · adj(B))` without any
commutativity or determinant hypothesis. -/
theorem sl2c_trace_adjugate_identity_noncomm {R : Type*} [Ring R]
    (A B : Matrix (Fin 2) (Fin 2) R) :
    A.trace * B.trace = (A * B).trace + (A * adjugate2 B).trace := by
  simp [adjugate2, Matrix.trace, Matrix.mul_apply, Fin.sum_univ_two]
  noncomm_ring

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
