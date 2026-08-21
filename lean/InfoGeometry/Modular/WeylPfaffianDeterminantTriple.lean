import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

noncomputable section

open Matrix

namespace InfoGeometry.Modular.Triple

variable {ι: Type*} [Fintype ι] [DecidableEq ι]

local notation "n" => Fintype.card ι

section AlgebraicHomomorphisms

variable {R: Type*} [CommRing R]
local notation "SubMat" => Matrix ι ι R

def totalDet (A D: SubMat) : R :=
  Matrix.det A * Matrix.det D

theorem totalDet_mul (A₁ A₂ D₁ D₂: SubMat) :
    totalDet (A₁ * A₂) (D₁ * D₂) = totalDet A₁ D₁ * totalDet A₂ D₂ := by
  dsimp [totalDet]
  rw [Matrix.det_mul, Matrix.det_mul]
  ring

variable {F: Type*} [Field F]
local notation "FieldMat" => Matrix ι ι F

def berezinian (A D: FieldMat) : F :=
  Matrix.det A / Matrix.det D

theorem berezinian_mul (A₁ A₂ D₁ D₂: FieldMat) :
    berezinian (A₁ * A₂) (D₁ * D₂) = berezinian A₁ D₁ * berezinian A₂ D₂ := by
  dsimp [berezinian]
  rw [Matrix.det_mul, Matrix.det_mul]
  exact mul_div_mul_comm (Matrix.det A₁) (Matrix.det A₂) (Matrix.det D₁) (Matrix.det D₂)

theorem berezinian_weyl_invariant (s: F) (hs: s ≠ 0) :
    berezinian (s • (1: FieldMat)) (s • (1: FieldMat)) = 1 := by
  dsimp [berezinian]
  have h_det_nonzero : Matrix.det (s • (1: FieldMat)) ≠ 0 := by
    rw [Matrix.det_smul, Matrix.det_one, mul_one]
    exact pow_ne_zero n hs
  exact div_self h_det_nonzero

end AlgebraicHomomorphisms

section AnalyticBarriers

local notation "RealMat" => Matrix ι ι ℝ

def barrierVol (A D: RealMat) : ℝ :=
  - Real.log (Matrix.det A * Matrix.det D)

def barrierChir (A D: RealMat) : ℝ :=
  - Real.log (berezinian A D)

theorem barrierVol_eq_sum (A D: RealMat) (hA: 0 < Matrix.det A) (hD: 0 < Matrix.det D) :
    barrierVol A D = - Real.log (Matrix.det A) - Real.log (Matrix.det D) := by
  dsimp [barrierVol]
  rw [Real.log_mul (ne_of_gt hA) (ne_of_gt hD)]
  ring

theorem barrierChir_eq_sub (A D: RealMat) (hA: 0 < Matrix.det A) (hD: 0 < Matrix.det D) :
    barrierChir A D = - Real.log (Matrix.det A) + Real.log (Matrix.det D) := by
  dsimp [barrierChir, berezinian]
  rw [Real.log_div (ne_of_gt hA) (ne_of_gt hD)]
  ring

theorem log_det_plus_reconstruction (A D: RealMat) (hA: 0 < Matrix.det A) (hD: 0 < Matrix.det D) :
    Real.log (Matrix.det A) = - (1 / 2: ℝ) * (barrierVol A D + barrierChir A D) := by
  rw [barrierVol_eq_sum A D hA hD, barrierChir_eq_sub A D hA hD]
  ring

theorem log_det_minus_reconstruction (A D: RealMat) (hA: 0 < Matrix.det A) (hD: 0 < Matrix.det D) :
    Real.log (Matrix.det D) = - (1 / 2: ℝ) * (barrierVol A D - barrierChir A D) := by
  rw [barrierVol_eq_sum A D hA hD, barrierChir_eq_sub A D hA hD]
  ring

theorem barrierChir_weyl_zero (s: ℝ) (hs: 0 < s) :
    barrierChir (s • (1: RealMat)) (s • (1: RealMat)) = 0 := by
  dsimp [barrierChir]
  rw [berezinian_weyl_invariant s (ne_of_gt hs), Real.log_one, neg_zero]

end AnalyticBarriers

end InfoGeometry.Modular.Triple

end noncomputable section
