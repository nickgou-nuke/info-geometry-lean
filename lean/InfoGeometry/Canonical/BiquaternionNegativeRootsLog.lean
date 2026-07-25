import Mathlib

open Matrix Complex

/-!
# Negative identity roots in the Pauli/biquaternion algebra

Maintained owner for the finite Pauli/biquaternion algebra recovered from the
external-auto and removable-disk lanes. This module keeps only the explicit
matrix algebra: Pauli vectors with quadratic norm `-1` square to `-I`, and the
integer logarithm branch shifts add as expected.
-/

noncomputable section

namespace BiquaternionNegativeRootsLog

/-- Pauli σ₁. -/
def σ₁ : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]

/-- Pauli σ₂. -/
def σ₂ : Matrix (Fin 2) (Fin 2) ℂ := !![0, -I; I, 0]

/-- Pauli σ₃. -/
def σ₃ : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]

/-- Traceless Pauli/biquaternion vector part. -/
def T (x y z : ℂ) : Matrix (Fin 2) (Fin 2) ℂ := x • σ₁ + y • σ₂ + z • σ₃

/-- The Pauli squaring identity `T² = (x²+y²+z²)I`. -/
theorem T_sq (x y z : ℂ) :
    T x y z * T x y z = (x * x + y * y + z * z) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [T, σ₁, σ₂, σ₃, Matrix.smul_apply, Matrix.add_apply,
      Matrix.mul_apply, Matrix.one_apply, Fin.sum_univ_two] <;>
    (ring_nf; try simp [Complex.I_mul_I]; try ring)

/-- If the Pauli vector has complex quadratic norm `-1`, it is a square root of `-I`. -/
theorem traceless_square_root_neg_one (x y z : ℂ) (h : x * x + y * y + z * z = -1) :
    T x y z * T x y z = -(1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  rw [T_sq, h]
  ext i j <;> fin_cases i <;> fin_cases j <;> simp [Matrix.smul_apply, Matrix.neg_apply]

/-- Scalar spinorial square root: `(iI)²=-I`. -/
theorem scalar_i_square_root_neg_one :
    (I • (1 : Matrix (Fin 2) (Fin 2) ℂ)) * (I • (1 : Matrix (Fin 2) (Fin 2) ℂ)) =
      -(1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [Matrix.smul_apply, Matrix.mul_apply, Matrix.one_apply, Matrix.neg_apply,
      Fin.sum_univ_two, Complex.I_mul_I]

/-- Concrete non-scalar spinorial square root: `(i σ₂)²=-I`. -/
theorem iσ₂_square_root_neg_one :
    (I • σ₂) * (I • σ₂) = -(1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [σ₂, Matrix.smul_apply, Matrix.mul_apply, Matrix.one_apply, Matrix.neg_apply,
      Fin.sum_univ_two, Complex.I_mul_I]

/-- The logarithm branch shift is indexed by integers: changing branch adds `2πi n`. -/
def logBranchShift (n : ℤ) : ℂ := (2 * Real.pi * n : ℝ) * I

/-- Opposite logarithm branches differ additively by the corresponding integer shift. -/
theorem logBranchShift_add (m n : ℤ) :
    logBranchShift (m + n) = logBranchShift m + logBranchShift n := by
  unfold logBranchShift
  norm_num
  ring

/-- Synthesis: scalar and traceless roots of `-I` coexist in `M₂(ℂ)`. -/
theorem negative_identity_root_synthesis :
    ((I • (1 : Matrix (Fin 2) (Fin 2) ℂ)) * (I • (1 : Matrix (Fin 2) (Fin 2) ℂ)) =
      -(1 : Matrix (Fin 2) (Fin 2) ℂ)) ∧
    ((I • σ₂) * (I • σ₂) = -(1 : Matrix (Fin 2) (Fin 2) ℂ)) := by
  exact ⟨scalar_i_square_root_neg_one, iσ₂_square_root_neg_one⟩

end BiquaternionNegativeRootsLog
