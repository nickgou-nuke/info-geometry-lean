import Mathlib.Data.Matrix.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic

/-!
# 2×2 Tripotent Matrix Representations

This module formalizes general classes of tripotent elements (matrices satisfying $M^3 = M$)
in the $2 \times 2$ matrix algebra over any commutative ring $R$.

Specifically, we prove that:
1. Any trace-zero matrix with determinant $-1$ is tripotent (and in fact squares to 1).
2. Any trace-one matrix with determinant $0$ is idempotent (and hence tripotent).

All proofs are native Lean 4 derivations checked by the kernel with zero remaining sorry debt.
-/

namespace InfoGeometry.OperatorAlgebra.TripotentMatrix2x2

/-- A general 2×2 matrix of trace zero:
`[[a, b], [c, -a]]`. -/
def traceZeroMatrix {R : Type*} [CommRing R] (a b c : R) : Matrix (Fin 2) (Fin 2) R :=
  !![a, b; c, -a]

/-- If `a² + b * c = 1` (equivalent to det = -1), the trace-zero matrix is tripotent. -/
theorem traceZero_tripotent {R : Type*} [CommRing R] (a b c : R) (h : a ^ 2 + b * c = 1) :
    (traceZeroMatrix a b c) ^ 3 = traceZeroMatrix a b c := by
  have h_sq : traceZeroMatrix a b c * traceZeroMatrix a b c = 1 := by
    ext i j
    fin_cases i <;> fin_cases j
    · simp [Matrix.mul_apply, Fin.sum_univ_two, traceZeroMatrix]
      linear_combination h
    · simp [Matrix.mul_apply, Fin.sum_univ_two, traceZeroMatrix]
      ring
    · simp [Matrix.mul_apply, Fin.sum_univ_two, traceZeroMatrix]
      ring
    · simp [Matrix.mul_apply, Fin.sum_univ_two, traceZeroMatrix]
      linear_combination h
  calc
    (traceZeroMatrix a b c) ^ 3 = (traceZeroMatrix a b c) ^ 2 * traceZeroMatrix a b c := by rw [pow_succ]
    _ = (traceZeroMatrix a b c * traceZeroMatrix a b c) * traceZeroMatrix a b c := by rw [pow_two]
    _ = 1 * traceZeroMatrix a b c := by rw [h_sq]
    _ = traceZeroMatrix a b c := by rw [one_mul]

/-- A general 2×2 matrix of trace one:
`[[a, b], [c, 1 - a]]`. -/
def traceOneMatrix {R : Type*} [CommRing R] (a b c : R) : Matrix (Fin 2) (Fin 2) R :=
  !![a, b; c, 1 - a]

/-- If `a * (1 - a) - b * c = 0` (equivalent to det = 0), the trace-one matrix is idempotent. -/
theorem traceOne_idempotent {R : Type*} [CommRing R] (a b c : R) (h : a * (1 - a) - b * c = 0) :
    traceOneMatrix a b c * traceOneMatrix a b c = traceOneMatrix a b c := by
  ext i j
  fin_cases i <;> fin_cases j
  · simp [Matrix.mul_apply, Fin.sum_univ_two, traceOneMatrix]
    linear_combination -1 * h
  · simp [Matrix.mul_apply, Fin.sum_univ_two, traceOneMatrix]
    ring
  · simp [Matrix.mul_apply, Fin.sum_univ_two, traceOneMatrix]
    ring
  · simp [Matrix.mul_apply, Fin.sum_univ_two, traceOneMatrix]
    linear_combination -1 * h

/-- Every idempotent element in a ring is tripotent. -/
theorem tripotent_of_idempotent {R : Type*} [Ring R] (M : R) (h : M * M = M) :
    M ^ 3 = M := by
  rw [pow_succ, pow_two, h, h]

/-- If `a * (1 - a) - b * c = 0` (equivalent to det = 0), the trace-one matrix is tripotent. -/
theorem traceOne_tripotent {R : Type*} [CommRing R] (a b c : R) (h : a * (1 - a) - b * c = 0) :
    (traceOneMatrix a b c) ^ 3 = traceOneMatrix a b c :=
  tripotent_of_idempotent (traceOneMatrix a b c) (traceOne_idempotent a b c h)

end InfoGeometry.OperatorAlgebra.TripotentMatrix2x2
