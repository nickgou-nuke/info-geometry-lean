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

theorem modularFlowTopologicalColimitMap_isIso (t : ℝ) :
    IsIso (modularFlowTopologicalColimitMap Stage T Φ t) := by
  exact (modularFlowTopologicalColimitIso Stage T Φ t).isIso_hom

end InfoGeometry.Canonical.CuntzStageModularFlowTopologicalIso
