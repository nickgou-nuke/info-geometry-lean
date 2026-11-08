/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Canonical.CuntzStageModularFlowTopologicalIso

noncomputable section

namespace InfoGeometry.Canonical.CuntzStageModularFlowTopologicalIso

open CategoryTheory
open InfoGeometry.Canonical.CuntzStarInductiveSystem
open InfoGeometry.Canonical.CuntzStageModularFlow
open InfoGeometry.Canonical.CuntzStageModularFlowTopologicalColimit
open InfoGeometry.Canonical.FilteredStarAlgebraTopologicalColimit

variable (Stage : ℕ → Type)
variable [∀ n, CStarAlgebra (Stage n)]
variable [∀ n, PartialOrder (Stage n)]
variable [∀ n, StarOrderedRing (Stage n)]
variable (T : CuntzStarTower Stage)
variable (Φ : CuntzStageModularFlowData Stage T)

/-- The generic topological Cuntz modular-flow isomorphisms compose in forward
 time order. -/
theorem modularFlowTopologicalColimitIso_comp_forward (t s : ℝ) :
    modularFlowTopologicalColimitIso Stage T Φ t ≪≫
        modularFlowTopologicalColimitIso Stage T Φ s =
      modularFlowTopologicalColimitIso Stage T Φ (t + s) := by
  calc
    modularFlowTopologicalColimitIso Stage T Φ t ≪≫
          modularFlowTopologicalColimitIso Stage T Φ s =
        modularFlowTopologicalColimitIso Stage T Φ (s + t) :=
      (modularFlowTopologicalColimitIso_add Stage T Φ s t).symm
    _ = modularFlowTopologicalColimitIso Stage T Φ (t + s) := by
      rw [add_comm s t]

end InfoGeometry.Canonical.CuntzStageModularFlowTopologicalIso
