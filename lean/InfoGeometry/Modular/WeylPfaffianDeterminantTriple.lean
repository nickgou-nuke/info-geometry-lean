import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-!
# The Weyl–Pfaffian–Determinant Triple and Logarithmic Surprisal Barriers

This module formalizes:
1. Total Determinant Homomorphism: det_tot(M₁ M₂) = det_tot(M₁) * det_tot(M₂).
2. Berezinian / Chiral Ratio Homomorphism: Ber(M₁ M₂) = Ber(M₁) * Ber(M₂).
3. Berezinian Weyl-Invariance: Ber(s • I, s • I) = 1.
4. Logarithmic Surprisal / Self-Concordant Barriers:
     Φ_vol = - log(det_tot)
     Φ_chir = - log(Ber)
5. Exact Reconstruction of Chiral Sector Log-Determinants from the Barriers.

All proofs are complete in native Mathlib with zero `sorry`s and zero custom axioms.
-/

noncomputable section

open Matrix

namespace InfoGeometry.Modular.Triple

variable {ι: Type*} [Fintype ι] [DecidableEq ι]

local notation "n" => Fintype.card ι

/-!
=============================================================================
PART 1: The Multiplicative Invariant Homomorphisms
=============================================================================
-/

section AlgebraicHomomorphisms

variable {R: Type*} [CommRing R]
local notation "SubMat" => Matrix ι ι R

/-- Total Determinant on the doubled block space: det_tot(A, D) = det(A) * det(D). -/
def totalDet (A D: SubMat) : R :=
  Matrix.det A * Matrix.det D

/-- 
  THEOREM 1: The Total Determinant is a Multiplicative Group Homomorphism:
  det_tot(A₁ A₂, D₁ D₂) = det_tot(A₁, D₁) * det_tot(A₂, D₂)
-/
theorem totalDet_mul (A₁ A₂ D₁ D₂: SubMat) :
    totalDet (A₁ * A₂) (D₁ * D₂) = totalDet A₁ D₁ * totalDet A₂ D₂ := by
  dsimp [totalDet]
  rw [Matrix.det_mul, Matrix.det_mul]
  ring

variable {F: Type*} [Field F]
local notation "FieldMat" => Matrix ι ι F

/-- 
  The Berezinian / Chiral Ratio:
  Ber(A, D) = det(A) / det(D)
-/
def berezinian (A D: FieldMat) : F :=
  Matrix.det A / Matrix.det D

/-- 
  THEOREM 2: The Berezinian is a Multiplicative Group Homomorphism:
  Ber(A₁ A₂, D₁ D₂) = Ber(A₁, D₁) * Ber(A₂, D₂)
-/
theorem berezinian_mul (A₁ A₂ D₁ D₂: FieldMat) :
    berezinian (A₁ * A₂) (D₁ * D₂) = berezinian A₁ D₁ * berezinian A₂ D₂ := by
  dsimp [berezinian]
  rw [Matrix.det_mul, Matrix.det_mul]
  exact mul_div_mul_comm (Matrix.det A₁) (Matrix.det A₂) (Matrix.det D₁) (Matrix.det D₂)

/-- 
  THEOREM 3 (Berezinian Weyl Invariance):
  Isotropic scaling by s preserves the Berezinian:
  Ber(s • I, s • I) = 1  for all s ≠ 0.
-/
theorem berezinian_weyl_invariant (s: F) (hs: s ≠ 0) :
    berezinian (s • (1: FieldMat)) (s • (1: FieldMat)) = 1 := by
  dsimp [berezinian]
  have h_det_nonzero : Matrix.det (s • (1: FieldMat)) ≠ 0 := by
    rw [Matrix.det_smul, Matrix.det_one, mul_one]
    exact pow_ne_zero n hs
  exact div_self h_det_nonzero

end AlgebraicHomomorphisms

/-!
=============================================================================
PART 2: Logarithmic Surprisals and Self-Concordant Barriers
=============================================================================
-/

section AnalyticBarriers

local notation "RealMat" => Matrix ι ι ℝ

/-- The Volume Surprisal / Self-Concordant Barrier: Φ_vol = - log(det_tot). -/
def barrierVol (A D: RealMat) : ℝ :=
  - Real.log (Matrix.det A * Matrix.det D)

/-- The Chiral Surprisal / Supervolume Barrier: Φ_chir = - log(Ber). -/
def barrierChir (A D: RealMat) : ℝ :=
  - Real.log (berezinian A D)

/-- 
  THEOREM 4: Expansion of the Volume Barrier into Component Log-Determinants:
  Φ_vol(A, D) = - log(det A) - log(det D)
-/
theorem barrierVol_eq_sum (A D: RealMat) (hA: 0 < Matrix.det A) (hD: 0 < Matrix.det D) :
    barrierVol A D = - Real.log (Matrix.det A) - Real.log (Matrix.det D) := by
  dsimp [barrierVol]
  rw [Real.log_mul (ne_of_gt hA) (ne_of_gt hD)]
  ring

/-- 
  THEOREM 5: Expansion of the Chiral Barrier into Component Log-Determinants:
  Φ_chir(A, D) = - log(det A) + log(det D)
-/
theorem barrierChir_eq_sub (A D: RealMat) (hA: 0 < Matrix.det A) (hD: 0 < Matrix.det D) :
    barrierChir A D = - Real.log (Matrix.det A) + Real.log (Matrix.det D) := by
  dsimp [barrierChir, berezinian]
  rw [Real.log_div (ne_of_gt hA) (ne_of_gt hD)]
  ring

/-- 
  THEOREM 6: Exact Reconstruction of the Positive Sector Log-Determinant:
  log(det A) = - (1/2) * (Φ_vol + Φ_chir)
-/
theorem log_det_plus_reconstruction (A D: RealMat) (hA: 0 < Matrix.det A) (hD: 0 < Matrix.det D) :
    Real.log (Matrix.det A) = - (1 / 2: ℝ) * (barrierVol A D + barrierChir A D) := by
  rw [barrierVol_eq_sum A D hA hD, barrierChir_eq_sub A D hA hD]
  ring

/-- 
  THEOREM 7: Exact Reconstruction of the Negative Sector Log-Determinant:
  log(det D) = - (1/2) * (Φ_vol - Φ_chir)
-/
theorem log_det_minus_reconstruction (A D: RealMat) (hA: 0 < Matrix.det A) (hD: 0 < Matrix.det D) :
    Real.log (Matrix.det D) = - (1 / 2: ℝ) * (barrierVol A D - barrierChir A D) := by
  rw [barrierVol_eq_sum A D hA hD, barrierChir_eq_sub A D hA hD]
  ring

/-- 
  THEOREM 8: Pure Weyl Dilation has Zero Chiral Barrier:
  Φ_chir(s • I, s • I) = 0  for all s > 0.
-/
theorem barrierChir_weyl_zero (s: ℝ) (hs: 0 < s) :
    barrierChir (s • (1: RealMat)) (s • (1: RealMat)) = 0 := by
  dsimp [barrierChir]
  rw [berezinian_weyl_invariant s (ne_of_gt hs), Real.log_one, neg_zero]

end AnalyticBarriers

end InfoGeometry.Modular.Triple

end noncomputable section
