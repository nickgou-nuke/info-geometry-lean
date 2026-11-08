/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Canonical.CuntzStageModularFlowColimit

noncomputable section

namespace InfoGeometry.Canonical.CuntzStageModularFlowColimit

open CategoryTheory CategoryTheory.Limits
open InfoGeometry.Canonical.CuntzStarInductiveSystem
open InfoGeometry.Canonical.CuntzStageModularFlow
open InfoGeometry.Canonical.CuntzStageModularFlow.CuntzStageModularFlowLemmas

variable (Stage : ℕ → Type)
variable [∀ n, CStarAlgebra (Stage n)]
variable [∀ n, PartialOrder (Stage n)]
variable (T : CuntzStarTower Stage)
variable (Φ : CuntzStageModularFlowData Stage T)

/-- Opposite-time modular flows are mutual inverses after descent to the
native `ModuleCat` colimit. -/
theorem modularFlowColimitMap_right_inverse (t : ℝ) :
    modularFlowColimitMap Stage T Φ t ≫
        modularFlowColimitMap Stage T Φ (-t) = 𝟙 _ := by
  rw [← modularFlowColimitMap_add Stage T Φ (-t) t]
  simpa using modularFlowColimitMap_zero Stage T Φ

theorem modularFlowColimitMap_left_inverse (t : ℝ) :
    modularFlowColimitMap Stage T Φ (-t) ≫
        modularFlowColimitMap Stage T Φ t = 𝟙 _ := by
  rw [← modularFlowColimitMap_add Stage T Φ t (-t)]
  simpa using modularFlowColimitMap_zero Stage T Φ

/-- The descended generic Cuntz modular flow is an actual categorical
isomorphism at every time. -/
theorem modularFlowColimitMap_isIso (t : ℝ) :
    IsIso (modularFlowColimitMap Stage T Φ t) := by
  let e :
      (colimit (stageModuleDiagram Stage T) : ModuleCat ℂ) ≅
        (colimit (stageModuleDiagram Stage T) : ModuleCat ℂ) :=
    { hom := modularFlowColimitMap Stage T Φ t
      inv := modularFlowColimitMap Stage T Φ (-t)
      hom_inv_id := modularFlowColimitMap_right_inverse Stage T Φ t
      inv_hom_id := modularFlowColimitMap_left_inverse Stage T Φ t }
  exact e.isIso_hom

end InfoGeometry.Canonical.CuntzStageModularFlowColimit
