import InfoGeometry.Canonical.DyadicDimensionGroup
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.RealStageProjectionRankDoubling

namespace InfoGeometry.Canonical

/-!
# Normalized projection rank on the binary stage tower

The finite rank doubles at each binary stage, so dividing by `2^n` gives a
stage-independent dyadic rational.  This is the concrete dimension-group
readout; no `K₀` or `KO₀` identification is used.
-/

noncomputable def normalizedProjectionRank {n : ℕ}
    (p : IdempotentProjection ℝ (RealStageVector n)) : ℚ :=
  (projectionRank p.map : ℚ) / (2 : ℚ) ^ n

theorem normalizedProjectionRank_isDyadic {n : ℕ}
    (p : IdempotentProjection ℝ (RealStageVector n)) :
    (normalizedProjectionRank p : ℚ) ∈ dyadicRational := by
  change ∃ z : ℤ, ∃ k : ℕ,
    normalizedProjectionRank p = (z : ℚ) / (2 : ℚ) ^ k
  exact ⟨projectionRank p.map, n, rfl⟩

theorem normalizedProjectionRank_nonneg {n : ℕ}
    (p : IdempotentProjection ℝ (RealStageVector n)) :
    0 ≤ normalizedProjectionRank p := by
  unfold normalizedProjectionRank
  positivity

theorem normalizedProjectionRank_le_one {n : ℕ}
    (p : IdempotentProjection ℝ (RealStageVector n)) :
    normalizedProjectionRank p ≤ 1 := by
  unfold normalizedProjectionRank
  have hrank : projectionRank p.map ≤ 2 ^ n :=
    projectionRank_le_realStageVector p.map
  have hrankQ : (projectionRank p.map : ℚ) ≤ ((2 ^ n : ℕ) : ℚ) := by
    exact_mod_cast hrank
  have hden : (0 : ℚ) < (2 : ℚ) ^ n := by positivity
  apply (div_le_iff₀ hden).2
  simpa using hrankQ

theorem normalizedProjectionRank_nextStage {n : ℕ}
    (p : IdempotentProjection ℝ (RealStageVector n)) :
    normalizedProjectionRank (nextStageProjectionData p) =
      normalizedProjectionRank p := by
  unfold normalizedProjectionRank
  rw [nextStageProjectionData_rank]
  have hn : (2 : ℚ) ^ n ≠ 0 := by positivity
  rw [pow_succ]
  field_simp [hn]
  rw [Nat.cast_mul]
  ring

noncomputable def normalizedProjectionRankDyadic {n : ℕ}
    (p : IdempotentProjection ℝ (RealStageVector n)) : DyadicRational :=
  ⟨normalizedProjectionRank p, normalizedProjectionRank_isDyadic p⟩

theorem normalizedProjectionRankDyadic_value {n : ℕ}
    (p : IdempotentProjection ℝ (RealStageVector n)) :
    (normalizedProjectionRankDyadic p : ℚ) = normalizedProjectionRank p := rfl

end InfoGeometry.Canonical
