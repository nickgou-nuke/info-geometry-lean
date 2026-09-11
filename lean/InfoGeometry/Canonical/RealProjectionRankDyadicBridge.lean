import InfoGeometry.Canonical.DyadicRankFamilyAdditive
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.RealProjectionRankConjugation

namespace InfoGeometry.Canonical

/-!
# Finite-stage projections to the concrete dyadic dimension group

The bridge is the forward representative/readout from the stage cocone.  It
does not identify this algebraic carrier with `K₀` or `KO₀`.
-/

noncomputable def projectionRankDimensionClass {n : ℕ}
    (p : IdempotentProjection ℝ (RealStageVector n)) : DyadicDirectLimit :=
  projectionDirectLimitReadout p

theorem projectionRankDimensionClass_readout {n : ℕ}
    (p : IdempotentProjection ℝ (RealStageVector n)) :
    dyadicDirectLimitEquiv (projectionRankDimensionClass p) =
      normalizedProjectionRankDyadic p := by
  unfold projectionRankDimensionClass projectionDirectLimitReadout
  exact dyadicDirectLimitEquiv.apply_symm_apply _

theorem projectionRankDimensionClass_stage_invariant {n : ℕ}
    (p : IdempotentProjection ℝ (RealStageVector n)) :
    projectionRankDimensionClass (nextStageProjectionData p) =
      projectionRankDimensionClass p := by
  exact projectionDirectLimitReadout_nextStage p

theorem projectionRankDimensionClass_value {n : ℕ}
    (p : IdempotentProjection ℝ (RealStageVector n)) :
    ((dyadicDirectLimitEquiv (projectionRankDimensionClass p) :
      DyadicRational) : ℚ) = normalizedProjectionRank p := by
  rw [projectionRankDimensionClass_readout]
  rfl

theorem normalizedProjectionRankDyadic_conjugate {n : ℕ}
    (e : RealStageVector n ≃ₗ[ℝ] RealStageVector n)
    (p q : IdempotentProjection ℝ (RealStageVector n))
    (hq : q.map = conjugateLinearMap e p.map) :
    normalizedProjectionRankDyadic q =
      normalizedProjectionRankDyadic p := by
  apply Subtype.ext
  change (projectionRank q.map : ℚ) / (2 : ℚ) ^ n =
    (projectionRank p.map : ℚ) / (2 : ℚ) ^ n
  rw [hq, projectionRank_conjugate]

end InfoGeometry.Canonical
