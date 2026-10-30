/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.ColimitContinuum.CartanActionOnMatrixTowerColimit

/-!
# Cartan root weights on the categorical matrix-tower colimit

The matrix tower embeddings preserve multiplication but are not unital, so the
categorical colimit used here is the actual Mathlib colimit in `ModuleCat R`.
This file descends the two noncommuting root operators as represented vectors
and proves their Cartan weights in that colimit. It does not endow the module
colimit with an algebra product.
-/

noncomputable section

namespace InfoGeometry.ColimitContinuum.RootWeightsOnMatrixTowerColimit

open CategoryTheory CategoryTheory.Limits
open InfoGeometry.ColimitContinuum.TensorTowerColimit
open InfoGeometry.ColimitContinuum.CartanActionOnMatrixTowerColimit

variable {R : Type} [CommRing R]

/-- The raising operator `E₀₂` at stage `n`; the tower embedding keeps it in
the same noncommutative corner at every later stage. -/
def raisingMatrix : (n : ℕ) → Stage (R := R) n
  | 0 => E3 0 2
  | n + 1 => embed_tower (raisingMatrix n)

/-- The lowering operator `E₂₀` at stage `n`. -/
def loweringMatrix : (n : ℕ) → Stage (R := R) n
  | 0 => E3 2 0
  | n + 1 => embed_tower (loweringMatrix n)

private theorem base_raising_weight :
    ad_H (R := R) 1 (raisingMatrix (R := R) 0) =
      (2 : R) • raisingMatrix (R := R) 0 := by
  ext i j
  fin_cases i
  all_goals fin_cases j
  all_goals
    simp [ad_H, H_tower, ad,
      InfoGeometry.ColimitContinuum.TensorTowerColimit.commutator,
      H_3, raisingMatrix, InfoGeometry.ColimitContinuum.TensorTowerColimit.E3,
      Matrix.mul_apply] <;> ring

private theorem base_lowering_weight :
    ad_H (R := R) 1 (loweringMatrix (R := R) 0) =
      -((2 : R) • loweringMatrix (R := R) 0) := by
  ext i j
  fin_cases i
  all_goals fin_cases j
  all_goals
    simp [ad_H, H_tower, ad,
      InfoGeometry.ColimitContinuum.TensorTowerColimit.commutator,
      H_3, loweringMatrix, InfoGeometry.ColimitContinuum.TensorTowerColimit.E3,
      Matrix.mul_apply] <;> ring

/-- The raising matrix is a weight `+2` vector at every finite tower stage. -/
theorem raisingMatrix_cartan_weight (n : ℕ) :
    ad_H (R := R) (n + 1) (raisingMatrix (R := R) n) =
      (2 : R) • raisingMatrix (R := R) n := by
  induction n with
  | zero => exact base_raising_weight (R := R)
  | succ n ih =>
      calc
        ad_H (R := R) (n + 2) (raisingMatrix (R := R) (n + 1)) =
            ad_H (R := R) (n + 2) (embed_tower (raisingMatrix (R := R) n)) := rfl
        _ = embed_tower (ad_H (R := R) (n + 1) (raisingMatrix (R := R) n)) :=
          (embed_tower_ad_H (R := R) n (raisingMatrix (R := R) n)).symm
        _ = embed_tower ((2 : R) • raisingMatrix (R := R) n) := by rw [ih]
        _ = (2 : R) • raisingMatrix (R := R) (n + 1) := by
          rw [embed_tower_smul]
          rfl

/-- The lowering matrix is a weight `-2` vector at every finite tower stage. -/
theorem loweringMatrix_cartan_weight (n : ℕ) :
    ad_H (R := R) (n + 1) (loweringMatrix (R := R) n) =
      -((2 : R) • loweringMatrix (R := R) n) := by
  induction n with
  | zero => exact base_lowering_weight (R := R)
  | succ n ih =>
      calc
        ad_H (R := R) (n + 2) (loweringMatrix (R := R) (n + 1)) =
            ad_H (R := R) (n + 2) (embed_tower (loweringMatrix (R := R) n)) := rfl
        _ = embed_tower (ad_H (R := R) (n + 1) (loweringMatrix (R := R) n)) :=
          (embed_tower_ad_H (R := R) n (loweringMatrix (R := R) n)).symm
        _ = embed_tower (-((2 : R) • loweringMatrix (R := R) n)) := by rw [ih]
        _ = -((2 : R) • loweringMatrix (R := R) (n + 1)) := by
          have hneg (x : Stage (R := R) n) : embed_tower (-x) = -embed_tower x := by
            calc
              embed_tower (-x) = embed_tower (0 - x) := by simp
              _ = embed_tower 0 - embed_tower x := embed_tower_sub 0 x
              _ = -embed_tower x := by rw [embed_tower_zero]; simp
          rw [hneg, embed_tower_smul]
          rfl

/-- The represented raising root vector in the actual categorical module
colimit. -/
def raisingRoot (n : ℕ) : TowerColimit (R := R) :=
  (stageInclusion (R := R) n).hom (raisingMatrix (R := R) n)

/-- The represented lowering root vector in the actual categorical module
colimit. -/
def loweringRoot (n : ℕ) : TowerColimit (R := R) :=
  (stageInclusion (R := R) n).hom (loweringMatrix (R := R) n)

/-- The descended Cartan action has weight `+2` on every represented raising
root vector in the actual categorical colimit. -/
theorem cartanColimit_raisingRoot_weight (n : ℕ) :
    (cartanColimitEndomorphism (R := R)).hom (raisingRoot (R := R) n) =
      (2 : R) • raisingRoot (R := R) n := by
  rw [raisingRoot, cartanColimitEndomorphism_apply_stage,
    raisingMatrix_cartan_weight]
  exact (stageInclusion (R := R) n).hom.map_smul _ _

/-- The descended Cartan action has weight `-2` on every represented lowering
root vector in the actual categorical colimit. -/
theorem cartanColimit_loweringRoot_weight (n : ℕ) :
    (cartanColimitEndomorphism (R := R)).hom (loweringRoot (R := R) n) =
      -((2 : R) • loweringRoot (R := R) n) := by
  rw [loweringRoot, cartanColimitEndomorphism_apply_stage,
    loweringMatrix_cartan_weight]
  let f := (stageInclusion (R := R) n).hom
  have harg : -((2 : R) • loweringMatrix (R := R) n) =
      (-((2 : R))) • loweringMatrix (R := R) n := (neg_smul _ _).symm
  rw [harg]
  calc
    f ((-((2 : R))) • loweringMatrix (R := R) n) =
        (-((2 : R))) • f (loweringMatrix (R := R) n) := f.map_smul _ _
    _ = -( (2 : R) • f (loweringMatrix (R := R) n)) := neg_smul _ _

end InfoGeometry.ColimitContinuum.RootWeightsOnMatrixTowerColimit

end
