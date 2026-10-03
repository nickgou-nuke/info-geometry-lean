import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

namespace InfoGeometry.Modular.DeterminantTrifactorHomomorphism

open Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

local notation "n" => Fintype.card ι
local notation "RealMat" => Matrix ι ι ℝ
local notation "ComplexMat" => Matrix ι ι ℂ

/-- 
  1. The Scale Character (Weyl trace): Extracts the volume scaling factor $\mathbb{R}^+$.
-/
noncomputable def extractScale (A : RealMat) : ℝ :=
  |Matrix.det A|

/-- 
  2. The Parity Character (Möbius sign): Extracts the discrete topological sign $\mathbb{Z}_2$.
-/
noncomputable def extractParity (A : RealMat) : ℝ :=
  if Matrix.det A > 0 then 1 else if Matrix.det A < 0 then -1 else 0

/-- 
  3. The Chiral Volume (Dirac phase): Extracts the phase $U(1)$ from the complexified determinant.
-/
noncomputable def extractChiralPhase (A : ComplexMat) : ℂ :=
  if Matrix.det A = 0 then 0 else (Matrix.det A) / ↑(Real.sqrt (Complex.normSq (Matrix.det A)))

/-- 
  The Scale Character is a multiplicative homomorphism.
-/
theorem scale_mul (A B : RealMat) :
    extractScale (A * B) = extractScale A * extractScale B := by
  dsimp [extractScale]
  rw [Matrix.det_mul, abs_mul]

/-- 
  The Parity Character is a multiplicative homomorphism.
-/
theorem parity_mul (A B : RealMat) (hA : Matrix.det A ≠ 0) (hB : Matrix.det B ≠ 0) :
    extractParity (A * B) = extractParity A * extractParity B := by
  dsimp [extractParity]
  have hd : Matrix.det (A * B) = Matrix.det A * Matrix.det B := Matrix.det_mul A B
  rw [hd]
  rcases lt_trichotomy (Matrix.det A) 0 with hA_neg | hA_zero | hA_pos
  · rcases lt_trichotomy (Matrix.det B) 0 with hB_neg | hB_zero | hB_pos
    · have h_mul_pos : Matrix.det A * Matrix.det B > 0 := mul_pos_of_neg_of_neg hA_neg hB_neg
      rw [if_pos h_mul_pos, if_neg (not_lt_of_gt hA_neg), if_pos hA_neg]
      rw [if_neg (not_lt_of_gt hB_neg), if_pos hB_neg]
      ring
    · exfalso; exact hB hB_zero
    · have h_mul_neg : Matrix.det A * Matrix.det B < 0 := mul_neg_of_neg_of_pos hA_neg hB_pos
      rw [if_neg (not_lt_of_gt h_mul_neg), if_pos h_mul_neg]
      rw [if_neg (not_lt_of_gt hA_neg), if_pos hA_neg, if_pos hB_pos]
      ring
  · exfalso; exact hA hA_zero
  · rcases lt_trichotomy (Matrix.det B) 0 with hB_neg | hB_zero | hB_pos
    · have h_mul_neg : Matrix.det A * Matrix.det B < 0 := mul_neg_of_pos_of_neg hA_pos hB_neg
      rw [if_neg (not_lt_of_gt h_mul_neg), if_pos h_mul_neg]
      rw [if_pos hA_pos, if_neg (not_lt_of_gt hB_neg), if_pos hB_neg]
      ring
    · exfalso; exact hB hB_zero
    · have h_mul_pos : Matrix.det A * Matrix.det B > 0 := mul_pos hA_pos hB_pos
      rw [if_pos h_mul_pos, if_pos hA_pos, if_pos hB_pos]
      ring

/-- 
  The full reconstruction: The real determinant is exactly the product of Scale and Parity.
-/
theorem real_det_reconstruction (A : RealMat) (hA : Matrix.det A ≠ 0) :
    Matrix.det A = extractScale A * extractParity A := by
  dsimp [extractScale, extractParity]
  rcases lt_trichotomy (Matrix.det A) 0 with h_neg | h_zero | h_pos
  · rw [if_neg (not_lt_of_gt h_neg), if_pos h_neg]
    have h_abs : |Matrix.det A| = -Matrix.det A := abs_of_neg h_neg
    rw [h_abs]; ring
  · exfalso; exact hA h_zero
  · rw [if_pos h_pos]
    have h_abs : |Matrix.det A| = Matrix.det A := abs_of_pos h_pos
    rw [h_abs, mul_one]

/-- 
  Complex reconstruction: The complex determinant is exactly Scale * Phase.
-/
noncomputable def extractComplexScale (A : ComplexMat) : ℝ :=
  Real.sqrt (Complex.normSq (Matrix.det A))

theorem complex_det_reconstruction (A : ComplexMat) (hA : Matrix.det A ≠ 0) :
    Matrix.det A = ↑(extractComplexScale A) * extractChiralPhase A := by
  dsimp [extractComplexScale, extractChiralPhase]
  rw [if_neg hA]
  have h_norm_pos : 0 < Complex.normSq (Matrix.det A) := Complex.normSq_pos.mpr hA
  have h_sqrt_nz : Real.sqrt (Complex.normSq (Matrix.det A)) ≠ 0 := Real.sqrt_ne_zero'.mpr h_norm_pos
  have h_abs_nz : (↑(Real.sqrt (Complex.normSq (Matrix.det A))) : ℂ) ≠ 0 := by
    rw [Complex.ofReal_ne_zero]
    exact h_sqrt_nz
  exact (mul_div_cancel₀ (Matrix.det A) h_abs_nz).symm

end InfoGeometry.Modular.DeterminantTrifactorHomomorphism
