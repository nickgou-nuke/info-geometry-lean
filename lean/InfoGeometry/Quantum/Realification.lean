/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Basic.Complex.BigOperators
import Mathlib.LinearAlgebra.Complex.Module
import Mathlib.Data.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Tactic.Ring

/-!
# Realification of full finite complex matrix algebras

The arbitrary-index extension of the repository's phase-first finite block
realification. Matrix multiplication retains its order throughout. The state
normalization and tensor combination rules are supplied by downstream owners.
-/

noncomputable section

open scoped BigOperators

namespace InfoGeometry.Quantum.Realification

variable {l m n : Type*}

/-- Replace each complex matrix by its real and imaginary phase blocks. -/
def realify (A : Matrix m n ℂ) : Matrix (m ⊕ m) (n ⊕ n) ℝ :=
  Matrix.fromBlocks (A.map Complex.re) (-(A.map Complex.im))
    (A.map Complex.im) (A.map Complex.re)

@[simp] theorem realify_inl_inl (A : Matrix m n ℂ) (i : m) (j : n) :
    realify A (Sum.inl i) (Sum.inl j) = (A i j).re := rfl

@[simp] theorem realify_inl_inr (A : Matrix m n ℂ) (i : m) (j : n) :
    realify A (Sum.inl i) (Sum.inr j) = -(A i j).im := rfl

@[simp] theorem realify_inr_inl (A : Matrix m n ℂ) (i : m) (j : n) :
    realify A (Sum.inr i) (Sum.inl j) = (A i j).im := rfl

@[simp] theorem realify_inr_inr (A : Matrix m n ℂ) (i : m) (j : n) :
    realify A (Sum.inr i) (Sum.inr j) = (A i j).re := rfl

@[simp] theorem realify_zero : realify (0 : Matrix m n ℂ) = 0 := by
  ext i j
  cases i <;> cases j <;> simp

@[simp] theorem realify_add (A B : Matrix m n ℂ) :
    realify (A + B) = realify A + realify B := by
  ext i j
  cases i <;> cases j <;> simp [add_comm]

@[simp] theorem realify_neg (A : Matrix m n ℂ) :
    realify (-A) = -realify A := by
  ext i j
  cases i <;> cases j <;> simp

@[simp] theorem realify_sub (A B : Matrix m n ℂ) :
    realify (A - B) = realify A - realify B := by
  simp only [sub_eq_add_neg, realify_add, realify_neg]

@[simp] theorem realify_smul (r : ℝ) (A : Matrix m n ℂ) :
    realify (r • A) = r • realify A := by
  ext i j
  cases i <;> cases j <;> simp

/-- Adjoint complex operators become transposed real operators. -/
@[simp] theorem realify_conjTranspose (A : Matrix m n ℂ) :
    realify A.conjTranspose = (realify A).transpose := by
  ext i j
  cases i <;> cases j <;> simp [Matrix.conjTranspose_apply]

/-- The equivalent statement using the native real adjoint. -/
theorem realify_star (A : Matrix m n ℂ) :
    realify A.conjTranspose = (realify A).conjTranspose := by
  simp

/-- Read a complex matrix from the first block column. -/
def unrealify (A : Matrix (m ⊕ m) (n ⊕ n) ℝ) : Matrix m n ℂ :=
  fun i j => ⟨A (Sum.inl i) (Sum.inl j), A (Sum.inr i) (Sum.inl j)⟩

@[simp] theorem unrealify_realify (A : Matrix m n ℂ) :
    unrealify (realify A) = A := by
  ext i j
  rfl

theorem realify_injective : Function.Injective (realify (m := m) (n := n)) := by
  intro A B h
  simpa only [unrealify_realify] using congrArg unrealify h

/-- Multiplication is preserved on rectangular matrices, with no commutation
hypothesis on either factor. -/
@[simp] theorem realify_mul [Fintype n]
    (A : Matrix m n ℂ) (B : Matrix n l ℂ) :
    realify (A * B) = realify A * realify B := by
  ext i j
  cases i <;> cases j <;>
    simp [Matrix.mul_apply, Fintype.sum_sum_type,
      Complex.re_sum, Complex.im_sum, Complex.mul_re, Complex.mul_im,
      Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_neg_distrib] <;>
    ring

@[simp] theorem realify_one [DecidableEq n] :
    realify (1 : Matrix n n ℂ) = 1 := by
  ext i j
  cases i <;> cases j <;>
    simp [Matrix.one_apply, apply_ite]

/-- The real trace doubles the real part of the complex trace. -/
theorem trace_realify [Fintype n] (A : Matrix n n ℂ) :
    Matrix.trace (realify A) = 2 * (Matrix.trace A).re := by
  simp [Matrix.trace, Matrix.diag, Fintype.sum_sum_type, Complex.re_sum,
    two_mul]

/-- The faithful real representation as a unital ring homomorphism. -/
def realifyRingHom [Fintype n] [DecidableEq n] :
    Matrix n n ℂ →+* Matrix (n ⊕ n) (n ⊕ n) ℝ where
  toFun := realify
  map_zero' := realify_zero
  map_one' := realify_one
  map_add' := realify_add
  map_mul' := realify_mul

/-- Real scalar linearity of the faithful matrix representation. -/
def realifyLinearMap :
    Matrix m n ℂ →ₗ[ℝ] Matrix (m ⊕ m) (n ⊕ n) ℝ where
  toFun := realify
  map_add' := realify_add
  map_smul' := realify_smul

@[simp] theorem realify_sum {ι : Type*} (s : Finset ι) (A : ι → Matrix m n ℂ) :
    realify (∑ i ∈ s, A i) = ∑ i ∈ s, realify (A i) :=
  map_sum realifyLinearMap A s

/-- The faithful embedding reflects, as well as preserves, commutation. -/
theorem realify_commute_iff [Fintype n] (A B : Matrix n n ℂ) :
    Commute (realify A) (realify B) ↔ Commute A B := by
  change realify A * realify B = realify B * realify A ↔ A * B = B * A
  rw [← realify_mul, ← realify_mul]
  exact realify_injective.eq_iff

/-- The real internal phase axis, defined without complex coefficients. -/
def internalJ [DecidableEq n] : Matrix (n ⊕ n) (n ⊕ n) ℝ :=
  Matrix.fromBlocks (0 : Matrix n n ℝ) (-1) 1 0

/-- The internal real axis is precisely the image of multiplication by `i`. -/
theorem internalJ_eq_realify [DecidableEq n] :
    internalJ (n := n) = realify (Complex.I • (1 : Matrix n n ℂ)) := by
  ext i j
  cases i <;> cases j <;>
    simp [internalJ, Matrix.one_apply, apply_ite]

@[simp] theorem internalJ_sq [Fintype n] [DecidableEq n] :
    internalJ (n := n) * internalJ = -1 := by
  simp only [internalJ, Matrix.fromBlocks_multiply,
    mul_zero, zero_mul, zero_add, add_zero, mul_one, one_mul]
  ext i j
  cases i <;> cases j <;> simp [Matrix.one_apply]

/-- Every realified operator commutes with the internal complex axis. -/
theorem realify_commutes_internalJ [Fintype n] [DecidableEq n]
    (A : Matrix n n ℂ) :
    Commute (realify A) (internalJ (n := n)) := by
  change realify A * internalJ = internalJ * realify A
  simp [realify, internalJ, Matrix.fromBlocks_multiply]

private theorem mul_internalJ [Fintype n] [DecidableEq n]
    (A : Matrix (n ⊕ n) (n ⊕ n) ℝ) :
    A * internalJ = Matrix.fromBlocks A.toBlocks₁₂ (-A.toBlocks₁₁)
      A.toBlocks₂₂ (-A.toBlocks₂₁) := by
  conv_lhs => rw [← Matrix.fromBlocks_toBlocks A]
  simp [internalJ, Matrix.fromBlocks_multiply]

private theorem internalJ_mul [Fintype n] [DecidableEq n]
    (A : Matrix (n ⊕ n) (n ⊕ n) ℝ) :
    internalJ * A = Matrix.fromBlocks (-A.toBlocks₂₁) (-A.toBlocks₂₂)
      A.toBlocks₁₁ A.toBlocks₁₂ := by
  conv_lhs => rw [← Matrix.fromBlocks_toBlocks A]
  simp [internalJ, Matrix.fromBlocks_multiply]

/-- The commutant condition recovers both missing blocks exactly. -/
theorem realify_unrealify_of_commute [Fintype n] [DecidableEq n]
    (A : Matrix (n ⊕ n) (n ⊕ n) ℝ) (hA : Commute A internalJ) :
    realify (unrealify A) = A := by
  have h := hA.eq
  rw [mul_internalJ, internalJ_mul] at h
  have hb := Matrix.fromBlocks_inj.mp h
  have h₁₂ : A.toBlocks₁₂ = -A.toBlocks₂₁ := hb.1
  have h₁₁ : A.toBlocks₁₁ = A.toBlocks₂₂ := neg_injective hb.2.1
  ext i j
  cases i with
  | inl i =>
    cases j with
    | inl j => rfl
    | inr j =>
      exact (congrArg (fun M : Matrix n n ℝ => M i j) h₁₂).symm
  | inr i =>
    cases j with
    | inl j => rfl
    | inr j =>
      exact congrArg (fun M : Matrix n n ℝ => M i j) h₁₁

/-- A real doubled matrix represents a complex operator exactly when it
commutes with the internal phase axis. -/
theorem mem_range_realify_iff_commute [Fintype n] [DecidableEq n]
    (A : Matrix (n ⊕ n) (n ⊕ n) ℝ) :
    A ∈ Set.range (realify (m := n) (n := n)) ↔ Commute A internalJ := by
  constructor
  · rintro ⟨B, rfl⟩
    exact realify_commutes_internalJ B
  · intro hA
    exact ⟨unrealify A, realify_unrealify_of_commute A hA⟩

end InfoGeometry.Quantum.Realification
