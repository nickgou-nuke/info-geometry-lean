/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Clifford.Cl11StarAlgebraColimit
import Mathlib.Algebra.Lie.OfAssociative

/-!
# Faithful double-inner-action readback on the real matrix colimit

All actions are native `LieAlgebra.ad` endomorphisms of the full associative
algebra. The exact kernel at the limit is read at a common later matrix stage.
No metric, scalar eigenvalue, or spectral bound is assumed or asserted.
-/

noncomputable section

namespace InfoGeometry.OperatorAlgebra.PeirceStarColimitActions

attribute [local instance] LieRing.ofAssociativeRing LieAlgebra.ofAssociativeAlgebra

section Transport

variable {A B : Type*} [Ring A] [Algebra ℝ A] [StarRing A]
    [Ring B] [Algebra ℝ B] [StarRing B]

/-- The full negative double inner action is natural under a native star-algebra map. -/
theorem map_double_inner (f : A →⋆ₐ[ℝ] B) (N X : A) :
    f ((-(LieAlgebra.ad ℝ A N * LieAlgebra.ad ℝ A N)) X) =
      (-(LieAlgebra.ad ℝ B (f N) * LieAlgebra.ad ℝ B (f N))) (f X) := by
  change f (-(N * (N * X - X * N) - (N * X - X * N) * N)) =
    -(f N * (f N * f X - f X * f N) - (f N * f X - f X * f N) * f N)
  simp only [map_neg, map_sub, map_mul]

/-- Injectivity gives exact pullback of the native kernel, not merely containment. -/
theorem comap_ker_double_inner (f : A →⋆ₐ[ℝ] B)
    (hf : Function.Injective f) (N : A) :
    (LinearMap.ker (-(LieAlgebra.ad ℝ B (f N) * LieAlgebra.ad ℝ B (f N)))).comap
        f.toAlgHom.toLinearMap =
      LinearMap.ker (-(LieAlgebra.ad ℝ A N * LieAlgebra.ad ℝ A N)) := by
  ext X
  change (-(LieAlgebra.ad ℝ B (f N) * LieAlgebra.ad ℝ B (f N))) (f X) = 0 ↔
    (-(LieAlgebra.ad ℝ A N * LieAlgebra.ad ℝ A N)) X = 0
  rw [← map_double_inner f, ← map_zero f, hf.eq_iff]

end Transport

open InfoGeometry.Clifford.Cl11TensorTowerLimit
open InfoGeometry.Clifford.Cl11StarAlgebraColimit
open InfoGeometry.Algebra.DirectLimitSuperClosureLemmas

/-- Canonical matrix inclusions reflect the full double-inner-action kernel. -/
theorem stage_ker_double_inner (n : ℕ) (N : Stage n) :
    (LinearMap.ker (-(LieAlgebra.ad ℝ Limit (ofStage n N) *
      LieAlgebra.ad ℝ Limit (ofStage n N)))).comap
        (ofStageStarAlgHom n).toAlgHom.toLinearMap =
      LinearMap.ker (-(LieAlgebra.ad ℝ (Stage n) N * LieAlgebra.ad ℝ (Stage n) N)) :=
  comap_ker_double_inner (ofStageStarAlgHom n) (ofStageStarAlgHom_injective n) N

/-- A kernel equation for any limit input is exactly a finite equation at some
common later stage, with the coefficient transported by the actual bonding map. -/
theorem limit_double_inner_eq_zero_iff (n : ℕ) (N : Stage n) (X : Limit) :
    (-(LieAlgebra.ad ℝ Limit (ofStage n N) *
      LieAlgebra.ad ℝ Limit (ofStage n N))) X = 0 ↔
      ∃ (m : ℕ) (h : n ≤ m) (Y : Stage m), ofStage m Y = X ∧
        (-(LieAlgebra.ad ℝ (Stage m) (bondMap stageBond n m h N) *
          LieAlgebra.ad ℝ (Stage m) (bondMap stageBond n m h N))) Y = 0 := by
  constructor
  · intro hX
    induction X using DirectLimit.induction with
    | _ k A =>
      let m := max n k
      let Y : Stage m := bondMap stageBond k m (le_max_right n k) A
      have hY : ofStage m Y = ofStage k A :=
        directLimitOf_bondMap stageBond k m (le_max_right n k) A
      have hN : ofStage m (bondMap stageBond n m (le_max_left n k) N) =
          ofStage n N :=
        directLimitOf_bondMap stageBond n m (le_max_left n k) N
      have hmap := map_double_inner (ofStageStarAlgHom m)
        (bondMap stageBond n m (le_max_left n k) N) Y
      simp only [ofStageStarAlgHom_apply] at hmap
      refine ⟨m, le_max_left n k, Y, hY, ?_⟩
      apply (ofStage_eq_zero_iff m _).mp
      rw [hmap, hN, hY]
      exact hX
  · rintro ⟨m, h, Y, hY, hD⟩
    have hN : ofStage m (bondMap stageBond n m h N) = ofStage n N :=
      directLimitOf_bondMap stageBond n m h N
    have hmap := map_double_inner (ofStageStarAlgHom m) (bondMap stageBond n m h N) Y
    simp only [ofStageStarAlgHom_apply] at hmap
    rw [← hY, ← hN, ← hmap, hD, map_zero]

end InfoGeometry.OperatorAlgebra.PeirceStarColimitActions
