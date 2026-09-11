import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.RealUHFProjectionRankSystem
import InfoGeometry.Canonical.RealUHFProjectionRankRealCompletionTopological

/-!
# Canonical endpoint projection systems

The zero and identity projections give two explicit coherent points of the
binary projection-rank tower.  Their normalized readouts are the two
endpoints of the real unit interval.  This owner does not assert that every
interior point is represented by a coherent projection system.
-/

noncomputable section

namespace InfoGeometry.Canonical.RealUHFProjectionRankCanonicalEndpoints

open InfoGeometry.Canonical
open InfoGeometry.Canonical.RealUHFProjectionRankRealCompletionTopological

theorem transportedDoubleProjection_zero (n : ℕ) :
    transportedDoubleProjection
        (0 : RealStageVector n →ₗ[ℝ] RealStageVector n) =
      0 := by
  apply LinearMap.ext
  intro x
  funext ij
  rcases ij with ⟨i, j⟩
  fin_cases j <;> rfl

theorem transportedDoubleProjection_id (n : ℕ) :
    transportedDoubleProjection
        (LinearMap.id : RealStageVector n →ₗ[ℝ] RealStageVector n) =
      LinearMap.id := by
  ext x
  simp [transportedDoubleProjection, doubleProjection]

noncomputable def zeroProjectionSystem :
    RealUHFProjectionRankSystem where
  projection := fun n => ⟨0, by simp⟩
  coherent := by
    intro n
    apply Subtype.ext
    exact transportedDoubleProjection_zero n

noncomputable def identityProjectionSystem :
    RealUHFProjectionRankSystem where
  projection := fun n => ⟨LinearMap.id, by simp⟩
  coherent := by
    intro n
    apply Subtype.ext
    exact transportedDoubleProjection_id n

theorem zeroProjectionSystem_readout (n : ℕ) :
    zeroProjectionSystem.normalizedReadout n =
      ⟨0, by
        refine ⟨0, 0, ?_⟩
        norm_num⟩ := by
  apply Subtype.ext
  unfold RealUHFProjectionRankSystem.normalizedReadout
  change (projectionRank
      (0 : RealStageVector n →ₗ[ℝ] RealStageVector n) : ℚ) /
        (2 : ℚ) ^ n = 0
  rw [projectionRank_zero]
  simp

theorem identityProjectionSystem_readout (n : ℕ) :
    identityProjectionSystem.normalizedReadout n =
      ⟨1, by
        refine ⟨1, 0, ?_⟩
        norm_num⟩ := by
  apply Subtype.ext
  unfold RealUHFProjectionRankSystem.normalizedReadout
  change normalizedProjectionRank
      (identityProjectionSystem.projection n) = 1
  unfold normalizedProjectionRank identityProjectionSystem
  rw [projectionRank_id, realStageVector_finrank]
  simp

theorem zeroProjectionSystem_realReadout (n : ℕ) :
    dyadicToRealInterval
        (zeroProjectionSystem.normalizedReadoutInterval n) =
      ⟨0, by norm_num⟩ := by
  apply Subtype.ext
  simp [dyadicToRealInterval,
    RealUHFProjectionRankSystem.normalizedReadoutInterval,
    zeroProjectionSystem_readout]

theorem identityProjectionSystem_realReadout (n : ℕ) :
    dyadicToRealInterval
        (identityProjectionSystem.normalizedReadoutInterval n) =
      ⟨1, by norm_num⟩ := by
  apply Subtype.ext
  simp [dyadicToRealInterval,
    RealUHFProjectionRankSystem.normalizedReadoutInterval,
    identityProjectionSystem_readout]

end RealUHFProjectionRankCanonicalEndpoints

end Canonical
