import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sign
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import InfoGeometry.Modular.WeylPfaffianDeterminantTriple

namespace InfoGeometry.Modular.DeterminantTrifactorHomomorphism

open Matrix
open InfoGeometry.Modular.Triple

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
local notation "RealMat" => Matrix ι ι ℝ

/-- 
  1. The Scale Character (Weyl trace): Extracts the continuous volume scaling factor $\mathbb{R}^+$.
-/
noncomputable def extractScale (A D : RealMat) : ℝ :=
  |totalDet A D|

/-- 
  2. The Parity Character (Möbius sign): Extracts the discrete topological sign $\mathbb{Z}_2$.
-/
noncomputable def extractParity (A D : RealMat) : ℝ :=
  if totalDet A D > 0 then 1 else if totalDet A D < 0 then -1 else 0

/-- 
  3. The Chiral Volume (Dirac phase): Extracts the Berezinian ratio measuring orientation twist.
-/
noncomputable def extractChiralPhase (A D : RealMat) : ℝ :=
  berezinian A D

/-- 
  The Scale Character is a multiplicative homomorphism.
-/
theorem scale_mul (A₁ A₂ D₁ D₂ : RealMat) :
    extractScale (A₁ * A₂) (D₁ * D₂) = extractScale A₁ D₁ * extractScale A₂ D₂ := by
  dsimp [extractScale]
  rw [totalDet_mul, abs_mul]

/-- 
  The Parity Character is a multiplicative homomorphism.
-/
theorem parity_mul (A₁ A₂ D₁ D₂ : RealMat) (h1 : totalDet A₁ D₁ ≠ 0) (h2 : totalDet A₂ D₂ ≠ 0) :
    extractParity (A₁ * A₂) (D₁ * D₂) = extractParity A₁ D₁ * extractParity A₂ D₂ := by
  dsimp [extractParity]
  rw [totalDet_mul]
  rcases lt_trichotomy (totalDet A₁ D₁) 0 with hA_neg | hA_zero | hA_pos
  · rcases lt_trichotomy (totalDet A₂ D₂) 0 with hB_neg | hB_zero | hB_pos
    · have h_mul_pos : totalDet A₁ D₁ * totalDet A₂ D₂ > 0 := mul_pos_of_neg_of_neg hA_neg hB_neg
      rw [if_pos h_mul_pos, if_neg (not_lt_of_gt hA_neg), if_pos hA_neg]
      rw [if_neg (not_lt_of_gt hB_neg), if_pos hB_neg]
      ring
    · exfalso; exact h2 hB_zero
    · have h_mul_neg : totalDet A₁ D₁ * totalDet A₂ D₂ < 0 := mul_neg_of_neg_of_pos hA_neg hB_pos
      rw [if_neg (not_lt_of_gt h_mul_neg), if_pos h_mul_neg]
      rw [if_neg (not_lt_of_gt hA_neg), if_pos hA_neg, if_pos hB_pos]
      ring
  · exfalso; exact h1 hA_zero
  · rcases lt_trichotomy (totalDet A₂ D₂) 0 with hB_neg | hB_zero | hB_pos
    · have h_mul_neg : totalDet A₁ D₁ * totalDet A₂ D₂ < 0 := mul_neg_of_pos_of_neg hA_pos hB_neg
      rw [if_neg (not_lt_of_gt h_mul_neg), if_pos h_mul_neg]
      rw [if_pos hA_pos, if_neg (not_lt_of_gt hB_neg), if_pos hB_neg]
      ring
    · exfalso; exact h2 hB_zero
    · have h_mul_pos : totalDet A₁ D₁ * totalDet A₂ D₂ > 0 := mul_pos hA_pos hB_pos
      rw [if_pos h_mul_pos, if_pos hA_pos, if_pos hB_pos]
      ring

/-- 
  The Chiral Volume is a multiplicative homomorphism.
-/
theorem chiral_phase_mul (A₁ A₂ D₁ D₂ : RealMat) :
    extractChiralPhase (A₁ * A₂) (D₁ * D₂) = extractChiralPhase A₁ D₁ * extractChiralPhase A₂ D₂ := by
  exact berezinian_mul A₁ A₂ D₁ D₂

/-- 
  Trifactor Map Reconstruction: The full determinant of the positive sector `A` 
  can be explicitly extracted from Scale, Parity, and Chiral Phase.
-/
theorem sector_det_reconstruction (A D : RealMat) (hD : Matrix.det D ≠ 0) :
    (Matrix.det A) ^ 2 = (extractScale A D * extractParity A D) * extractChiralPhase A D := by
  dsimp [extractScale, extractParity, extractChiralPhase, totalDet, berezinian]
  have h_recon : |Matrix.det A * Matrix.det D| * (if Matrix.det A * Matrix.det D > 0 then 1 else if Matrix.det A * Matrix.det D < 0 then -1 else 0) = Matrix.det A * Matrix.det D := by
    rcases lt_trichotomy (Matrix.det A * Matrix.det D) 0 with h_neg | h_zero | h_pos
    · rw [if_neg (not_lt_of_gt h_neg), if_pos h_neg]
      have h_abs : |Matrix.det A * Matrix.det D| = -(Matrix.det A * Matrix.det D) := abs_of_neg h_neg
      rw [h_abs]; ring
    · rw [h_zero, if_neg (lt_irrefl 0), if_neg (lt_irrefl 0)]
      have h_abs : |(0:ℝ)| = 0 := abs_zero
      rw [h_abs]; ring
    · rw [if_pos h_pos]
      have h_abs : |Matrix.det A * Matrix.det D| = Matrix.det A * Matrix.det D := abs_of_pos h_pos
      rw [h_abs, mul_one]
  rw [h_recon]
  symm
  calc
    (Matrix.det A * Matrix.det D) * (Matrix.det A / Matrix.det D) = (Matrix.det A * Matrix.det A) * (Matrix.det D / Matrix.det D) := by ring
    _ = (Matrix.det A * Matrix.det A) * 1 := by rw [div_self hD]
    _ = Matrix.det A ^ 2 := by ring

end InfoGeometry.Modular.DeterminantTrifactorHomomorphism
