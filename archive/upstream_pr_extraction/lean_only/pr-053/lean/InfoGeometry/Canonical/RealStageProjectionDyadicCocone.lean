import InfoGeometry.Canonical.DyadicDimensionGroupUniversalProperty
import InfoGeometry.Canonical.RealStageNormalizedProjectionRank

/-!
# Dyadic readout of the native finite-stage projection transport

This owner packages the already-proved native vector-stage transport.  It does
not introduce a second matrix stage, a second projection predicate, or a
`K₀`-claim: the direct-limit carrier is `DyadicDirectLimit`, and its canonical
readout is the existing `dyadicDirectLimitEquiv`.
-/

namespace InfoGeometry.Canonical

noncomputable def projectionDyadicReadout {n : ℕ}
    (p : IdempotentProjection ℝ (RealStageVector n)) : DyadicRational :=
  normalizedProjectionRankDyadic p

@[simp]
theorem projectionDyadicReadout_value {n : ℕ}
    (p : IdempotentProjection ℝ (RealStageVector n)) :
    (projectionDyadicReadout p : ℚ) = normalizedProjectionRank p := by
  rfl

@[simp]
theorem projectionDyadicReadout_nextStage {n : ℕ}
    (p : IdempotentProjection ℝ (RealStageVector n)) :
    projectionDyadicReadout (nextStageProjectionData p) =
      projectionDyadicReadout p := by
  apply Subtype.ext
  exact normalizedProjectionRank_nextStage p

noncomputable def projectionDirectLimitReadout {n : ℕ}
    (p : IdempotentProjection ℝ (RealStageVector n)) : DyadicDirectLimit :=
  dyadicDirectLimitEquiv.symm (projectionDyadicReadout p)

@[simp]
theorem projectionDirectLimitReadout_nextStage {n : ℕ}
    (p : IdempotentProjection ℝ (RealStageVector n)) :
    projectionDirectLimitReadout (nextStageProjectionData p) =
      projectionDirectLimitReadout p := by
  simp [projectionDirectLimitReadout]

end InfoGeometry.Canonical
