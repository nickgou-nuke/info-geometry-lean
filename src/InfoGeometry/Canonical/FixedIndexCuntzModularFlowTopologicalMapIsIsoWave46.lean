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

/-- The fixed-index descended topological modular-flow map is invertible in
`TopCat`; its inverse is the opposite-time map already used by the native
isomorphism owner. -/
theorem flowTopologicalColimitMap_isIso (t : ℝ) :
    IsIso (flowTopologicalColimitMap Stage T Φ t) := by
  exact (flowTopologicalColimitIso Stage T Φ t).isIso_hom

end InfoGeometry.Canonical.FixedIndexCuntzModularFlowTopologicalIso
