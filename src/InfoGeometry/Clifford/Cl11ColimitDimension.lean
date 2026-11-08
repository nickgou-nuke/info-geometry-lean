/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Clifford.Cl11StarUniversal
import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Infinite dimension of the real matrix tensor colimit

Every full matrix stage embeds faithfully and real-linearly into the existing
limit. Its dimension is `4^n`; these dimensions have no finite upper bound.
The conclusion concerns the actual algebraic quotient, without a completion.
-/

namespace InfoGeometry.Clifford.Cl11ColimitDimension

open Cl11TensorTowerLimit Cl11StarUniversal TowerMatrix

/-- The full real matrix algebra at stage n has dimension `4^n`. -/
theorem finrank_stage (n : ℕ) : Module.finrank ℝ (Stage n) = 4 ^ n := by
  change Module.finrank ℝ (Matrix (Idx n) (Idx n) ℝ) = 4 ^ n
  rw [Module.finrank_matrix, Module.finrank_self, mul_one, idx_card_pow_two,
    ← mul_pow]
  norm_num

/-- Any finite-dimensional target of a faithful stage inclusion has at least
the dimension of that full matrix stage. -/
theorem stage_dimension_le {B : Type*} [AddCommGroup B] [Module ℝ B]
    [FiniteDimensional ℝ B] (n : ℕ) (f : Stage n →ₗ[ℝ] B)
    (hf : Function.Injective f) : 4 ^ n ≤ Module.finrank ℝ B := by
  rw [← finrank_stage n]
  exact LinearMap.finrank_le_finrank_of_injective hf

/-- The existing real tensor-limit quotient is genuinely infinite-dimensional. -/
theorem not_finiteDimensional : ¬ FiniteDimensional ℝ Limit := by
  intro h
  let _ := h
  let n := Module.finrank ℝ Limit
  have hbound : 4 ^ n ≤ n :=
    stage_dimension_le n (ofStageStarAlgHom n).toLinearMap
      (ofStageStarAlgHom_injective n)
  exact (Nat.lt_pow_self (by decide : 1 < 4)).not_ge hbound

end InfoGeometry.Clifford.Cl11ColimitDimension
