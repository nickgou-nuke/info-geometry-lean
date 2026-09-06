import InfoGeometry.Canonical.RealProjectionRankConjugation
import InfoGeometry.Canonical.RealStageKroneckerAction

namespace InfoGeometry.Canonical

/-!
# Projection-rank transport along the binary stage tower

An idempotent projection on the real stage vector space can be transported to
the next stage by duplicating its two tensor columns.  The transported map is
again idempotent, and its finite-dimensional range has twice the rank.

This is the finite algebraic rank system underlying the later dyadic
dimension-group construction.  It is not a `K₀` or `KO₀` statement.
-/

noncomputable def nextStageProjection {n : ℕ}
    (p : IdempotentProjection ℝ (RealStageVector n)) :
    RealStageVector (n + 1) →ₗ[ℝ] RealStageVector (n + 1) :=
  transportedDoubleProjection p.map

theorem nextStageProjection_idempotent {n : ℕ}
    (p : IdempotentProjection ℝ (RealStageVector n)) :
    (nextStageProjection p).comp (nextStageProjection p) =
      nextStageProjection p := by
  exact transportedDoubleProjection_idempotent p.idempotent

theorem nextStageProjection_rank {n : ℕ}
    (p : IdempotentProjection ℝ (RealStageVector n)) :
    projectionRank (nextStageProjection p) =
      2 * projectionRank p.map := by
  exact transportedDoubleProjection_rank p.map

noncomputable def nextStageProjectionData {n : ℕ}
    (p : IdempotentProjection ℝ (RealStageVector n)) :
    IdempotentProjection ℝ (RealStageVector (n + 1)) :=
  ⟨nextStageProjection p, nextStageProjection_idempotent p⟩

theorem nextStageProjectionData_rank {n : ℕ}
    (p : IdempotentProjection ℝ (RealStageVector n)) :
    projectionRank (nextStageProjectionData p).map =
      2 * projectionRank p.map := by
  exact nextStageProjection_rank p

end InfoGeometry.Canonical
