/-
Phase 1: Native mathlib-compatible `su(n)` Lie algebra definition.
- Defines `su n` as a real LieSubalgebra of `Matrix n n ℂ`.
- Carrier: {A : Matrix n n ℂ | A† = -A ∧ trace A = 0}
- Uses `Submodule.span` and `LieSubalgebra.mk` (structure extension).
-/

import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Algebra.Lie.Subalgebra
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.Module.Submodule.LinearMap

open Matrix
open LieAlgebra

namespace InfoGeometry.Algebra

/-- Carrier set for 𝔰𝔲(n): skew-Hermitian trace-zero complex matrices. -/
def suCarrier (n : Type*) [Fintype n] [DecidableEq n] : Set (Matrix n n ℂ) :=
  { A : Matrix n n ℂ | A.conjTranspose = -A ∧ Matrix.trace A = 0 }

/-- Real Lie subalgebra 𝔰𝔲(n) ⊆ Matrix n n ℂ -/
def su (n : Type*) [Fintype n] [DecidableEq n] : LieSubalgebra ℝ (Matrix n n ℂ) where
  carrier := suCarrier n
  add_mem' := by
    intro A B hA hB
    dsimp [suCarrier] at hA hB ⊢
    constructor
    · rw [Matrix.conjTranspose_add, hA.1, hB.1, neg_add]
    · rw [Matrix.trace_add, hA.2, hB.2, add_zero]
  zero_mem' := by
    dsimp [suCarrier]
    constructor
    · rw [Matrix.conjTranspose_zero, neg_zero]
    · rw [Matrix.trace_zero]
  smul_mem' := by
    intro c A hA
    dsimp [suCarrier] at hA ⊢
    constructor
    · rw [Matrix.conjTranspose_smul, hA.1, smul_neg, star_trivial]
    · rw [Matrix.trace_smul, hA.2, smul_zero]
  lie_mem' := by
    intro A B hA hB
    dsimp [suCarrier] at hA hB ⊢
    constructor
    · rw [LieRing.of_associative_ring_bracket, Matrix.conjTranspose_sub,
          Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hA.1, hB.1]
      ext i j
      simp [Matrix.sub_apply, Matrix.mul_apply, Matrix.neg_apply]
    · rw [LieRing.of_associative_ring_bracket, Matrix.trace_sub, Matrix.trace_mul_comm, sub_self]

/-- The inclusion 𝔰𝔲(n) → Matrix n n ℂ as a linear map. -/
def su_inclusion (n : Type*) [Fintype n] [DecidableEq n] :
    su n →ₗ[ℝ] Matrix n n ℂ :=
  (su n).toSubmodule.subtype

end InfoGeometry.Algebra
