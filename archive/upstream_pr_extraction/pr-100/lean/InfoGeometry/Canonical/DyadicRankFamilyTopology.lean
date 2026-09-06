import InfoGeometry.Canonical.RealProjectionRankDyadicBridge

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

end InfoGeometry.Canonical
