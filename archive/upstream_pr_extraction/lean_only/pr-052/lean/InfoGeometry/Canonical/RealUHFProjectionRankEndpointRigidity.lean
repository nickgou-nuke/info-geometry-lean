import Mathlib
import InfoGeometry.Canonical.RealUHFProjectionRankRealCompletionTopological
import InfoGeometry.Canonical.RealUHFProjectionRankSystem

/-!
# Endpoint rigidity of the anchored projection-rank tower

The coherent system is indexed from stage `0`, whose vector space has
dimension one.  Consequently every coherent normalized projection-rank
readout is forced to be an endpoint.  This is a structural fact about the
current anchored owner, not a statement about an unanchored dimension-group
carrier.
-/

noncomputable section

namespace InfoGeometry.Canonical.RealUHFProjectionRankEndpointRigidity

open InfoGeometry.Canonical
open InfoGeometry.Canonical.RealUHFProjectionRankRealCompletionTopological

theorem stage_zero_projection_rank_endpoint
    (S : RealUHFProjectionRankSystem) :
    projectionRank (S.projection 0).map = 0 ∨
      projectionRank (S.projection 0).map = 1 := by
  have hle : projectionRank (S.projection 0).map ≤ 1 := by
    simpa using projectionRank_le_realStageVector (S.projection 0).map
  omega

theorem normalizedReadout_value_endpoint
    (S : RealUHFProjectionRankSystem) (n : ℕ) :
    ((S.normalizedReadout n : DyadicRational) : ℚ) = 0 ∨
      ((S.normalizedReadout n : DyadicRational) : ℚ) = 1 := by
  have hzero :
      ((S.normalizedReadout 0 : DyadicRational) : ℚ) =
        (projectionRank (S.projection 0).map : ℚ) := by
    change (projectionRank (S.projection 0).map : ℚ) /
        (2 : ℚ) ^ 0 = _
    simp
  have hbase :
      ((S.normalizedReadout 0 : DyadicRational) : ℚ) = 0 ∨
        ((S.normalizedReadout 0 : DyadicRational) : ℚ) = 1 := by
    rcases stage_zero_projection_rank_endpoint S with h | h
    · left
      rw [hzero, h]
      norm_num
    · right
      rw [hzero, h]
      norm_num
  have hstable : S.normalizedReadout n = S.normalizedReadout 0 := by
    simpa using S.normalizedReadout_add 0 n
  rcases hbase with h | h
  · left
    rw [hstable]
    exact h
  · right
    rw [hstable]
    exact h

theorem normalizedReadoutInterval_real_endpoint
    (S : RealUHFProjectionRankSystem) (n : ℕ) :
    dyadicToRealInterval (S.normalizedReadoutInterval n) =
        ⟨0, by norm_num⟩ ∨
      dyadicToRealInterval (S.normalizedReadoutInterval n) =
        ⟨1, by norm_num⟩ := by
  rcases normalizedReadout_value_endpoint S n with h | h
  · left
    apply Subtype.ext
    simp [dyadicToRealInterval,
      RealUHFProjectionRankSystem.normalizedReadoutInterval, h]
  · right
    apply Subtype.ext
    simp [dyadicToRealInterval,
      RealUHFProjectionRankSystem.normalizedReadoutInterval, h]

end InfoGeometry.Canonical.RealUHFProjectionRankEndpointRigidity

end
