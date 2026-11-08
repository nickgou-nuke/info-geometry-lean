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

theorem flowTopologicalColimitIso_comp_inverse (t : ℝ) :
    flowTopologicalColimitIso Stage T Φ t ≪≫
        flowTopologicalColimitIso Stage T Φ (-t) =
      Iso.refl (topologicalColimit Stage (system Stage T)) := by
  apply CategoryTheory.Iso.ext
  exact flowTopologicalColimitMap_right_inverse Stage T Φ t

end InfoGeometry.Canonical.FixedIndexCuntzModularFlowTopologicalIso
