import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic

/-!
# The finite-dimensional obstruction to the canonical CCR

For positive finite dimension, no pair of square real matrices can satisfy
`A * B - B * A = 1`. The proof is the trace obstruction. This separates the
finite CAR matrix models from CCR representations on polynomial or other
infinite-dimensional algebraic modules; it does not make an analytic Hilbert
space claim.
-/

namespace InfoGeometry.SuperGrassmannian.FiniteCCRTraceObstruction

open Matrix

/-- Every commutator of square real matrices has trace zero. -/
theorem matrix_commutator_trace_eq_zero {n : ℕ}
    (A B : Matrix (Fin n) (Fin n) ℝ) :
    Matrix.trace (A * B - B * A) = 0 := by
  rw [Matrix.trace_sub, Matrix.trace_mul_comm B A, sub_self]

/-- A positive-dimensional square matrix commutator cannot equal the identity. -/
theorem matrix_commutator_ne_one {n : ℕ} (hn : 0 < n)
    (A B : Matrix (Fin n) (Fin n) ℝ) :
    A * B - B * A ≠ 1 := by
  intro h
  have htrace := congrArg Matrix.trace h
  rw [matrix_commutator_trace_eq_zero] at htrace
  have htrace_one : Matrix.trace (1 : Matrix (Fin n) (Fin n) ℝ) = (n : ℝ) := by
    simp [Matrix.trace]
  rw [htrace_one] at htrace
  have hn_real : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
  linarith

end InfoGeometry.SuperGrassmannian.FiniteCCRTraceObstruction
