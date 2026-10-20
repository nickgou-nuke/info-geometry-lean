/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Canonical.AlgebraicKMSStateColimit

noncomputable section
set_option autoImplicit false

namespace InfoGeometry.Canonical.AlgebraicKMSStateColimit

open InfoGeometry.Canonical.CuntzMatrixAlgebraicStarColimit
open InfoGeometry.Canonical.CuntzMatrixCompatibleStateNet
open InfoGeometry.Canonical.CuntzMatrixAlgebraicTraceFunctional
open InfoGeometry.Canonical.CuntzMatrixTraceTower
open InfoGeometry.Canonical.CuntzMatrixTowerInstantiation
open InfoGeometry.Canonical.FiniteMatrixGibbsFunctional

theorem normalizedDeltaWeightedFunctional_stage_eq_gibbsFunctional
    {n : ℕ} (H : MatrixStage n) (hH : H.IsHermitian) (β : ℝ)
    (x : MatrixStage n) :
    normalizedDeltaWeightedFunctional (stageUnitToColimit n
      (gibbsDensityUnit H hH β)) (stageInjection n x) =
      gibbsFunctional H hH β x := by
  rw [normalizedDeltaWeightedFunctional_apply,
    deltaWeightedFunctional_stage,
    stageUnitToColimit_coe,
    traceFunctional_stage,
    matrixTraceFunctional_apply,
    gibbsFunctional_apply]
  rw [gibbsDensityUnit_coe]
  rw [Matrix.trace_mul_comm]
  let z : ℂ := Matrix.trace (gibbsDensity H hH β)
  have hz : z ≠ 0 := gibbsPartition_ne_zero H hH β
  have hn : (2 ^ n : ℂ) ≠ 0 := by norm_num
  simp only [matrixTraceState_apply]
  dsimp [z] at hz ⊢
  field_simp [hz, hn]

end InfoGeometry.Canonical.AlgebraicKMSStateColimit
