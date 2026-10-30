/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# Power traces of Kronecker products: the product rule for partition functions

For square matrices `A : Matrix m m α` and `B : Matrix n n α` over a
commutative ring, the Kronecker product `A ⊗ₖ B` is a matrix in the
non-commutative ring `Matrix (m × n) (m × n) α`. Its powers factor as
`(A ⊗ₖ B)^k = A^k ⊗ₖ B^k`, so all power traces are multiplicative:

`tr((A ⊗ₖ B)^k) = tr(A^k) · tr(B^k)`.

This is the precise form of "the partition function of a composite system is
the product of the partition functions". It holds for every power-trace (moment)
`Z_k = tr(T^k)`, with no diagonalization and no commutation between `A` and `B`.
-/

namespace InfoGeometry.OperatorAlgebra.OperatorDirichlet

open Matrix
open scoped Kronecker

variable {α : Type*} [CommRing α] {m n : Type*} [Fintype m] [Fintype n]
  [DecidableEq m] [DecidableEq n]

theorem kronecker_pow (A : Matrix m m α) (B : Matrix n n α) (k : ℕ) :
    (A ⊗ₖ B) ^ k = (A ^ k) ⊗ₖ (B ^ k) := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ, ih, ← mul_kronecker_mul, ← pow_succ, ← pow_succ]

/-- Power traces of a Kronecker product multiply. -/
theorem trace_kronecker_pow (A : Matrix m m α) (B : Matrix n n α) (k : ℕ) :
    trace ((A ⊗ₖ B) ^ k) = trace (A ^ k) * trace (B ^ k) := by
  rw [kronecker_pow, trace_kronecker]

/-- The same for any polynomial-free weighted sum of power traces, e.g. a
truncated generating function `∑_{k<N} c_k tr(T^k)` evaluated factorwise. -/
theorem sum_trace_kronecker_pow (A : Matrix m m α) (B : Matrix n n α) (c : ℕ → α) (N : ℕ) :
    ∑ k ∈ Finset.range N, c k * trace ((A ⊗ₖ B) ^ k) =
      ∑ k ∈ Finset.range N, c k * (trace (A ^ k) * trace (B ^ k)) := by
  simp_rw [trace_kronecker_pow]

end InfoGeometry.OperatorAlgebra.OperatorDirichlet
