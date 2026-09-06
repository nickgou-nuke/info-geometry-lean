import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic

/-!
# Unitary covariance of finite Gram states

This is the matrix-level compatibility wire needed by a future concrete
representation of Cuntz label permutations.  It does not claim that a given
permutation is the polar factor of an affinity.
-/

noncomputable section

namespace InfoGeometry.Krein.CuntzPermutationGramModularBridge

open Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

abbrev Mat (n : Type*) := Matrix n n ℂ

def rightGram (C : Mat n) : Mat n := Cᴴ * C

def leftGram (C : Mat n) : Mat n := C * Cᴴ

/-- The right Gramian is self-adjoint. -/
theorem rightGram_conjTranspose (C : Mat n) :
    (rightGram C)ᴴ = rightGram C := by
  simp [rightGram]

/-- The left Gramian is self-adjoint. -/
theorem leftGram_conjTranspose (C : Mat n) :
    (leftGram C)ᴴ = leftGram C := by
  simp [leftGram]

def unitaryConjugate (U C : Mat n) : Mat n := U * C * Uᴴ

theorem rightGram_unitaryConjugate (U C : Mat n)
    (hU : Uᴴ * U = 1) :
    rightGram (unitaryConjugate U C) = U * rightGram C * Uᴴ := by
  simp only [rightGram, unitaryConjugate, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose]
  calc
    U * (Cᴴ * Uᴴ) * (U * C * Uᴴ) =
        U * Cᴴ * (Uᴴ * U) * C * Uᴴ := by noncomm_ring
    _ = U * (Cᴴ * C) * Uᴴ := by rw [hU]; noncomm_ring

theorem leftGram_unitaryConjugate (U C : Mat n)
    (hU : Uᴴ * U = 1) :
    leftGram (unitaryConjugate U C) = U * leftGram C * Uᴴ := by
  simp only [leftGram, unitaryConjugate, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose]
  calc
    U * C * Uᴴ * (U * (Cᴴ * Uᴴ)) =
        U * C * (Uᴴ * U) * Cᴴ * Uᴴ := by noncomm_ring
    _ = U * (C * Cᴴ) * Uᴴ := by rw [hU]; noncomm_ring

theorem trace_unitaryConjugate_rightGram (U C : Mat n)
    (hU : Uᴴ * U = 1) :
    Matrix.trace (rightGram (unitaryConjugate U C)) =
      Matrix.trace (rightGram C) := by
  rw [rightGram_unitaryConjugate U C hU]
  calc
    Matrix.trace (U * rightGram C * Uᴴ) =
        Matrix.trace (Uᴴ * (U * rightGram C)) := by
          rw [Matrix.trace_mul_comm]
    _ = Matrix.trace (rightGram C) := by rw [← mul_assoc, hU, one_mul]

def normalizedRightGram (C : Mat n) : Mat n :=
  (Matrix.trace (rightGram C))⁻¹ • rightGram C

theorem normalizedRightGram_unitaryConjugate (U C : Mat n)
    (hU : Uᴴ * U = 1) :
    normalizedRightGram (unitaryConjugate U C) =
      U * normalizedRightGram C * Uᴴ := by
  rw [normalizedRightGram, normalizedRightGram,
    trace_unitaryConjugate_rightGram U C hU,
    rightGram_unitaryConjugate U C hU]
  simp [smul_smul]

/-- A nonzero right Gramian trace makes the normalized Gramian trace one. -/
theorem trace_normalizedRightGram (C : Mat n)
    (hC : Matrix.trace (rightGram C) ≠ 0) :
    Matrix.trace (normalizedRightGram C) = 1 := by
  rw [normalizedRightGram, Matrix.trace_smul]
  simpa [one_div, smul_eq_mul] using inv_mul_cancel₀ hC

/-- Every diagonal Gramian entry has nonnegative real part. -/
theorem rightGram_diag_re_nonneg (C : Mat n) (i : n) :
    0 ≤ (rightGram C i i).re := by
  simp [rightGram, Matrix.mul_apply, Complex.mul_re]
  exact Finset.sum_nonneg fun x _ =>
    add_nonneg (mul_self_nonneg _) (mul_self_nonneg _)

/-- Scalar multiplication of a matrix scales its right Gramian by `star a * a`. -/
theorem rightGram_smul (a : ℂ) (C : Mat n) :
    rightGram (a • C) = (star a * a) • rightGram C := by
  rw [rightGram, Matrix.conjTranspose_smul, Matrix.smul_mul,
    Matrix.mul_smul, smul_smul]
  rfl

/-- The trace of the right Gramian has the same scalar covariance. -/
theorem trace_rightGram_smul (a : ℂ) (C : Mat n) :
    Matrix.trace (rightGram (a • C)) =
      (star a * a) * Matrix.trace (rightGram C) := by
  rw [rightGram_smul, Matrix.trace_smul]
  rfl

/-- Scalar multiplication of a matrix scales its left Gramian by `star a * a`. -/
theorem leftGram_smul (a : ℂ) (C : Mat n) :
    leftGram (a • C) = (star a * a) • leftGram C := by
  rw [leftGram, Matrix.conjTranspose_smul, Matrix.smul_mul,
    Matrix.mul_smul, smul_smul]
  rw [mul_comm a (star a)]
  rfl

/-- Every diagonal left-Gramian entry has nonnegative real part. -/
theorem leftGram_diag_re_nonneg (C : Mat n) (i : n) :
    0 ≤ (leftGram C i i).re := by
  simp [leftGram, Matrix.mul_apply, Complex.mul_re]
  exact Finset.sum_nonneg fun x _ =>
    add_nonneg (mul_self_nonneg _) (mul_self_nonneg _)

/-- The trace of the left Gramian has the same scalar covariance. -/
theorem trace_leftGram_smul (a : ℂ) (C : Mat n) :
    Matrix.trace (leftGram (a • C)) =
      (star a * a) * Matrix.trace (leftGram C) := by
  rw [leftGram_smul, Matrix.trace_smul]
  rfl

/-- The left and right Gramian have the same finite trace. -/
theorem trace_leftGram_eq_trace_rightGram (C : Mat n) :
    Matrix.trace (leftGram C) = Matrix.trace (rightGram C) := by
  rw [leftGram, rightGram, Matrix.trace_mul_comm]

end InfoGeometry.Krein.CuntzPermutationGramModularBridge
