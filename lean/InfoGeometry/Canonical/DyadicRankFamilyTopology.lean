/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.RealProjectionRankDyadicBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra

namespace InfoGeometry.Canonical

/-!
# Direct-limit readout topology

The topology belongs to the concrete dyadic readout, not to an auxiliary
inverse-limit family.
-/

noncomputable def dyadicDirectLimitValue (x : DyadicDirectLimit) : DyadicRational :=
  dyadicDirectLimitEquiv x

theorem dyadicDirectLimitValue_projectionRank {n : ℕ}
    (p : IdempotentProjection ℝ (RealStageVector n)) :
    dyadicDirectLimitValue (projectionRankDimensionClass p) =
      normalizedProjectionRankDyadic p := by
  exact projectionRankDimensionClass_readout p


abbrev DyadicRankFamilyValue := DyadicRational

end InfoGeometry.Canonical
