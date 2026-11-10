/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Data.Matrix.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic

/-!
# 2×2 Tripotent Matrix Representations over Non-Commutative Operator Rings

This module formalizes general classes of tripotent elements (matrices satisfying $M^3 = M$)
and their non-commutative commutator anomalies in the $2 \times 2$ matrix algebra over any
(not necessarily commutative) operator ring $R$.

Specifically, over any `[Ring R]` we prove:
1. `traceZeroMatrix_sq`: The square of `[[a, b], [c, -a]]` has diagonal entries
   `a^2 + b * c` and `c * b + a^2` and off-diagonal commutator anomaly entries
   `[a, b] = a * b - b * a` and `[c, a] = c * a - a * c`.
2. `traceZero_tripotent`: When `a^2 + b * c = 1`, `c * b + a^2 = 1`, and the
   off-diagonal commutators vanish (`a * b = b * a`, `c * a = a * c`), the
   trace-zero matrix squares to `1` and is tripotent (`M^3 = M`).
3. `traceOneMatrix_sq_sub_self`: The idempotence defect `M * M - M` of
   `[[a, b], [c, 1 - a]]` carries `[a, b] = a * b - b * a` and `[c, a] = c * a - a * c`
   in the off-diagonal slots.
4. `traceOne_idempotent` and `traceOne_tripotent`: Under vanishing of the diagonal
   and commutator defects, the trace-one matrix is idempotent and tripotent over `[Ring R]`.

All proofs are native Lean 4 derivations checked by the kernel with zero remaining sorry debt.
-/

namespace InfoGeometry.OperatorAlgebra.TripotentMatrix2x2

/-- A general 2×2 matrix of trace zero over any ring `R`:
`[[a, b], [c, -a]]`. -/
def traceZeroMatrix {R : Type*} [Ring R] (a b c : R) : Matrix (Fin 2) (Fin 2) R :=
  !![a, b; c, -a]

/-- Over a general non-commutative ring `R`, the square of `traceZeroMatrix a b c`
explicitly exhibits the operator commutators `[a, b] = a * b - b * a` and
`[c, a] = c * a - a * c` in the off-diagonal entries, and `a^2 + b * c` vs
`c * b + a^2` on the diagonal. -/
theorem traceZeroMatrix_sq {R : Type*} [Ring R] (a b c : R) :
    traceZeroMatrix a b c * traceZeroMatrix a b c =
      !![a ^ 2 + b * c, a * b - b * a; c * a - a * c, c * b + a ^ 2] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, traceZeroMatrix] <;>
    noncomm_ring

/-- Over any ring `R`, if `a² + b * c = 1`, `c * b + a² = 1`, `a * b = b * a`,
and `c * a = a * c`, the trace-zero matrix squares to `1` and is tripotent. -/
theorem traceZero_tripotent {R : Type*} [Ring R] (a b c : R)
    (h1 : a ^ 2 + b * c = 1) (h2 : c * b + a ^ 2 = 1)
    (hab : a * b = b * a) (hca : c * a = a * c) :
    (traceZeroMatrix a b c) ^ 3 = traceZeroMatrix a b c := by
  have h_sq : traceZeroMatrix a b c * traceZeroMatrix a b c = 1 := by
    rw [traceZeroMatrix_sq, h1, h2, sub_eq_zero.mpr hab, sub_eq_zero.mpr hca]
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  calc
    (traceZeroMatrix a b c) ^ 3 = (traceZeroMatrix a b c) ^ 2 * traceZeroMatrix a b c := by
      rw [pow_succ]
    _ = (traceZeroMatrix a b c * traceZeroMatrix a b c) * traceZeroMatrix a b c := by
      rw [pow_two]
    _ = 1 * traceZeroMatrix a b c := by rw [h_sq]
    _ = traceZeroMatrix a b c := by rw [one_mul]

/-- A general 2×2 matrix of trace one over any ring `R`:
`[[a, b], [c, 1 - a]]`. -/
def traceOneMatrix {R : Type*} [Ring R] (a b c : R) : Matrix (Fin 2) (Fin 2) R :=
  !![a, b; c, 1 - a]

/-- Over a general non-commutative ring `R`, the idempotence defect
`M * M - M` of `traceOneMatrix a b c` carries the off-diagonal commutator
anomalies `a * b - b * a` and `c * a - a * c`. -/
theorem traceOneMatrix_sq_sub_self {R : Type*} [Ring R] (a b c : R) :
    traceOneMatrix a b c * traceOneMatrix a b c - traceOneMatrix a b c =
      !![-(a * (1 - a) - b * c), a * b - b * a;
         c * a - a * c, -(a * (1 - a) - c * b)] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [traceOneMatrix] <;>
    noncomm_ring

/-- Over any ring `R`, if `a * (1 - a) - b * c = 0`, `a * (1 - a) - c * b = 0`,
`a * b = b * a`, and `c * a = a * c`, the trace-one matrix is idempotent. -/
theorem traceOne_idempotent {R : Type*} [Ring R] (a b c : R)
    (h1 : a * (1 - a) - b * c = 0) (h2 : a * (1 - a) - c * b = 0)
    (hab : a * b = b * a) (hca : c * a = a * c) :
    traceOneMatrix a b c * traceOneMatrix a b c = traceOneMatrix a b c := by
  have h_def := traceOneMatrix_sq_sub_self a b c
  rw [h1, h2, sub_eq_zero.mpr hab, sub_eq_zero.mpr hca, neg_zero] at h_def
  have h_zero : (!![(0 : R), 0; 0, 0] : Matrix (Fin 2) (Fin 2) R) = 0 := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [h_zero] at h_def
  exact sub_eq_zero.mp h_def

/-- Every idempotent element in a ring is tripotent. -/
theorem tripotent_of_idempotent {R : Type*} [Ring R] (M : R) (h : M * M = M) :
    M ^ 3 = M := by
  rw [pow_succ, pow_two, h, h]

/-- Over any ring `R`, if the diagonal and commutator defects vanish, the
trace-one matrix is tripotent. -/
theorem traceOne_tripotent {R : Type*} [Ring R] (a b c : R)
    (h1 : a * (1 - a) - b * c = 0) (h2 : a * (1 - a) - c * b = 0)
    (hab : a * b = b * a) (hca : c * a = a * c) :
    (traceOneMatrix a b c) ^ 3 = traceOneMatrix a b c :=
  tripotent_of_idempotent (traceOneMatrix a b c) (traceOne_idempotent a b c h1 h2 hab hca)

/-- Elementary 2×2 upper-triangular shift matrix over `R`. -/
def matE01 {R : Type*} [Ring R] : Matrix (Fin 2) (Fin 2) R :=
  !![0, 1; 0, 0]

/-- Elementary 2×2 lower-triangular shift matrix over `R`. -/
def matE10 {R : Type*} [Ring R] : Matrix (Fin 2) (Fin 2) R :=
  !![0, 0; 1, 0]

/-- Explicit non-commutativity witness for `Matrix (Fin 2) (Fin 2) R` over any nontrivial ring `R`. -/
theorem matE01_mul_matE10_ne_comm {R : Type*} [Ring R] [Nontrivial R] :
    matE01 (R := R) * matE10 (R := R) ≠ matE10 (R := R) * matE01 (R := R) := by
  intro h
  have h00 := congrFun (congrFun h 0) 0
  simp [matE01, matE10, Matrix.mul_apply, Fin.sum_univ_two] at h00

end InfoGeometry.OperatorAlgebra.TripotentMatrix2x2
