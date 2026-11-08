/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Canonical.FixedIndexCuntzModularFlowTopologicalIso

noncomputable section

namespace InfoGeometry.Canonical.FixedIndexCuntzModularFlowTopologicalIso

open CategoryTheory CategoryTheory.Limits
open InfoGeometry.Canonical.FixedIndexCuntzModularFlowColimit
open InfoGeometry.Canonical.FixedIndexCuntzModularFlowTopologicalColimit
open InfoGeometry.Canonical.FixedIndexCuntzStarTower
open InfoGeometry.Canonical.FilteredStarAlgebraTopologicalColimit
open FilteredColimit.Native.Topological

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (Stage : ℕ → Type)
variable [∀ n, CStarAlgebra (Stage n)]
variable [∀ n, PartialOrder (Stage n)]
variable [∀ n, StarOrderedRing (Stage n)]
variable (T : FixedIndexCuntzStarTower.Data (ι := ι) Stage)
variable (Φ : FlowData Stage T)

/-- The fixed-index topological Cuntz modular-flow isomorphisms compose in
forward time order. -/
theorem flowTopologicalColimitIso_comp_forward (t s : ℝ) :
    flowTopologicalColimitIso Stage T Φ t ≪≫
        flowTopologicalColimitIso Stage T Φ s =
      flowTopologicalColimitIso Stage T Φ (t + s) := by
  calc
    flowTopologicalColimitIso Stage T Φ t ≪≫
          flowTopologicalColimitIso Stage T Φ s =
        flowTopologicalColimitIso Stage T Φ (s + t) :=
      (flowTopologicalColimitIso_add Stage T Φ s t).symm
    _ = flowTopologicalColimitIso Stage T Φ (t + s) := by
      rw [add_comm s t]

end InfoGeometry.Canonical.FixedIndexCuntzModularFlowTopologicalIso
