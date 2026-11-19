/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
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
  1. The absolute total-determinant readout. It is positive on invertible blocks.
-/
noncomputable def extractScale (A D : RealMat) : ℝ :=
  |totalDet A D|

/-- 
  2. The real sign readout, taking values in `{-1, 0, 1}`. It is multiplicative
     only on the nonzero-determinant locus; it is not itself a `ZMod 2` map.
-/
private noncomputable def realSignReadout (x : ℝ) : ℝ :=
  if x > 0 then 1 else if x < 0 then -1 else 0

private theorem realSignReadout_mul {x y : ℝ} (hx : x ≠ 0) (hy : y ≠ 0) :
    realSignReadout (x * y) = realSignReadout x * realSignReadout y := by
  dsimp [realSignReadout]
  rcases lt_trichotomy x 0 with hx_neg | hx_zero | hx_pos
  · rcases lt_trichotomy y 0 with hy_neg | hy_zero | hy_pos
    · have hxy : x * y > 0 := mul_pos_of_neg_of_neg hx_neg hy_neg
      rw [if_pos hxy, if_neg (not_lt_of_gt hx_neg), if_pos hx_neg]
      rw [if_neg (not_lt_of_gt hy_neg), if_pos hy_neg]
      ring
    · exact (hy hy_zero).elim
    · have hxy : x * y < 0 := mul_neg_of_neg_of_pos hx_neg hy_pos
      rw [if_neg (not_lt_of_gt hxy), if_pos hxy]
      rw [if_neg (not_lt_of_gt hx_neg), if_pos hx_neg, if_pos hy_pos]
      ring
  · exact (hx hx_zero).elim
  · rcases lt_trichotomy y 0 with hy_neg | hy_zero | hy_pos
    · have hxy : x * y < 0 := mul_neg_of_pos_of_neg hx_pos hy_neg
      rw [if_neg (not_lt_of_gt hxy), if_pos hxy]
      rw [if_pos hx_pos, if_neg (not_lt_of_gt hy_neg), if_pos hy_neg]
      ring
    · exact (hy hy_zero).elim
    · have hxy : x * y > 0 := mul_pos hx_pos hy_pos
      rw [if_pos hxy, if_pos hx_pos, if_pos hy_pos]
      ring

private theorem abs_mul_realSignReadout (x : ℝ) :
    |x| * realSignReadout x = x := by
  dsimp [realSignReadout]
  rcases lt_trichotomy x 0 with hx_neg | hx_zero | hx_pos
  · rw [if_neg (not_lt_of_gt hx_neg), if_pos hx_neg, abs_of_neg hx_neg]
    ring
  · rw [hx_zero, if_neg (lt_irrefl 0), if_neg (lt_irrefl 0), abs_zero]
    ring
  · rw [if_pos hx_pos, abs_of_pos hx_pos]
    ring

noncomputable def extractParity (A D : RealMat) : ℝ :=
  realSignReadout (totalDet A D)

/-- 
  3. The real Berezinian ratio. It is not a unit-circle phase without further
     hypotheses or additional structure.
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
  change realSignReadout (totalDet (A₁ * A₂) (D₁ * D₂)) =
    realSignReadout (totalDet A₁ D₁) * realSignReadout (totalDet A₂ D₂)
  rw [totalDet_mul]
  exact realSignReadout_mul h1 h2

/-- 
  The real Berezinian ratio is multiplicative for these block readouts.
-/
theorem chiral_phase_mul (A₁ A₂ D₁ D₂ : RealMat) :
    extractChiralPhase (A₁ * A₂) (D₁ * D₂) = extractChiralPhase A₁ D₁ * extractChiralPhase A₂ D₂ := by
  exact berezinian_mul A₁ A₂ D₁ D₂

/-- 
  On the locus where `det D` is nonzero, the square of the determinant of `A`
  is reconstructed from the absolute total determinant, its real sign, and the
  real Berezinian ratio. This is a scalar identity, not a group isomorphism.
-/
theorem sector_det_reconstruction (A D : RealMat) (hD : Matrix.det D ≠ 0) :
    (Matrix.det A) ^ 2 = (extractScale A D * extractParity A D) * extractChiralPhase A D := by
  dsimp [extractScale, extractParity, extractChiralPhase]
  rw [abs_mul_realSignReadout]
  dsimp [totalDet, berezinian]
  field_simp

end InfoGeometry.Modular.DeterminantTrifactorHomomorphism
