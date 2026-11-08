import InfoGeometry.Canonical.RealUHFProjectionRankSystem
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.RealProjectionRankDyadicBridge

/-!
# Finite-stage representatives for the real dyadic rank system

This owner identifies the normalized rank class of a finite-stage projection
with its explicit stage representative.  It remains a statement about the
concrete dyadic dimension group; no `K₀`, `KO₀`, or completed UHF algebra is
introduced here.
-/

namespace InfoGeometry.Canonical.RealUHFProjectionRankStageBridge

open InfoGeometry.Canonical

theorem projectionRankDimensionClass_eq_stage {n : ℕ}
    (p : IdempotentProjection ℝ (RealStageVector n)) :
    projectionRankDimensionClass p =
      dyadicStage n (projectionRank p.map) := by
  apply dyadicDirectLimitEquiv.injective
  rw [projectionRankDimensionClass_readout]
  change normalizedProjectionRankDyadic p =
    dyadicStageMap n (projectionRank p.map)
  rfl

theorem projectionRankDimensionClass_nextStage_eq_transition
    {n : ℕ} (p : IdempotentProjection ℝ (RealStageVector n)) :
    projectionRankDimensionClass (nextStageProjectionData p) =
      dyadicStage (n + 1) (projectionRank (nextStageProjectionData p).map) := by
  exact projectionRankDimensionClass_eq_stage (nextStageProjectionData p)

end InfoGeometry.Canonical.RealUHFProjectionRankStageBridge
