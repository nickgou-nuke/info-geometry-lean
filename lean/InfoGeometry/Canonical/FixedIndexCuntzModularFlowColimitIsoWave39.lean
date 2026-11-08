/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Canonical.FixedIndexCuntzModularFlowColimit

noncomputable section

namespace InfoGeometry.Canonical.FixedIndexCuntzModularFlowColimit

open CategoryTheory CategoryTheory.Limits
open InfoGeometry.Canonical.FixedIndexCuntzStarTower
open FilteredColimit.Native

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (Stage : ℕ → Type)
variable [∀ n, CStarAlgebra (Stage n)]
variable [∀ n, PartialOrder (Stage n)]
variable [∀ n, StarOrderedRing (Stage n)]
variable (T : FixedIndexCuntzStarTower.Data (ι := ι) Stage)
variable (Φ : FlowData Stage T)

/-- The descended fixed-index modular flow is an actual categorical
isomorphism on the native module colimit; its inverse is the opposite-time
flow. -/
theorem flowColimitMap_isIso (t : ℝ) :
    IsIso (flowColimitMap Stage T Φ t) := by
  let e :
      (colimit (stageModuleDiagram Stage T) : ModuleCat ℂ) ≅
        (colimit (stageModuleDiagram Stage T) : ModuleCat ℂ) :=
    { hom := flowColimitMap Stage T Φ t
      inv := flowColimitMap Stage T Φ (-t)
      hom_inv_id := flowColimitMap_right_inverse Stage T Φ t
      inv_hom_id := flowColimitMap_left_inverse Stage T Φ t }
  exact e.isIso_hom

end InfoGeometry.Canonical.FixedIndexCuntzModularFlowColimit
