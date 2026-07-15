import InfoGeometry.External.Auto.BuresMetricClosedCartography

/-!
# Canonical Bures metric / Bloch-ball cartography owner

Maintained owner for the finite Bloch-ball density-matrix and Bures-distance
packet recovered from the external auto surface. This owner re-homes the proven
finite results under a canonical namespace so downstream code can depend on a
stable maintained surface while preserving the already-checked external proofs.

This file intentionally promotes only the executable finite-dimensional content:
explicit `2 × 2` density matrices, determinant/trace identities, the simplified
Bures metric used in the repository, and selected closed-form distance facts.
It does not promote the surrounding narrative analogies to categorical or
physical equivalences.
-/

noncomputable section

namespace InfoGeometry.Canonical.BuresMetricClosedCartography

abbrev I2 := _root_.I2
abbrev σ₁ := _root_.σ₁
abbrev σ₂ := _root_.σ₂
abbrev σ₃ := _root_.σ₃

abbrev densityMatrix := _root_.densityMatrix
abbrev densityMatrix_explicit := _root_.densityMatrix_explicit
abbrev densityMatrix_hermitian := _root_.densityMatrix_hermitian
abbrev trace_densityMatrix := _root_.trace_densityMatrix
abbrev det_densityMatrix := _root_.det_densityMatrix

abbrev blochRadius := _root_.blochRadius
abbrev isBlochBall := _root_.isBlochBall
abbrev isPureState := _root_.isPureState
abbrev pureState_iff_det_zero := _root_.pureState_iff_det_zero
abbrev isMaximallyMixed := _root_.isMaximallyMixed
abbrev maximallyMixed_is_identity_over_two := _root_.maximallyMixed_is_identity_over_two

abbrev buresMetric := _root_.buresMetric
abbrev buresMetric_pos := _root_.buresMetric_pos
abbrev buresMetric_diverges_at_boundary := _root_.buresMetric_diverges_at_boundary
abbrev buresMetric_at_origin := _root_.buresMetric_at_origin
abbrev buresMetric_neg_isometry := _root_.buresMetric_neg_isometry

abbrev fidelity := _root_.fidelity
abbrev buresDistance := _root_.buresDistance
abbrev buresDistance_nonneg := _root_.buresDistance_nonneg
abbrev buresDistance_eq_zero_iff := _root_.buresDistance_eq_zero_iff
abbrev buresDistance_pure_states := _root_.buresDistance_pure_states
abbrev buresDistance_maximally_mixed := _root_.buresDistance_maximally_mixed
abbrev buresDistance_center_to_boundary := _root_.buresDistance_center_to_boundary

abbrev holographicBoundary := _root_.holographicBoundary
abbrev ads_cft_from_two_by_two := _root_.ads_cft_from_two_by_two

abbrev RosettaStone := _root_.RosettaStone
abbrev rosetta_stone_principle := _root_.rosetta_stone_principle

/-- Maintained packet exposing the finite canonical Bures/Bloch owner surface. -/
theorem canonical_bures_cartography_packet
    (x y z dx dy dz : ℝ)
    (hball : x^2 + y^2 + z^2 < 1)
    (hvec : dx^2 + dy^2 + dz^2 > 0) :
    Matrix.trace (densityMatrix x y z) = 1 ∧
    Matrix.det (densityMatrix x y z) = ((1 - (x^2 + y^2 + z^2)) / 4 : ℝ) ∧
    0 < buresMetric x y z dx dy dz hball := by
  exact ⟨trace_densityMatrix x y z, det_densityMatrix x y z,
    buresMetric_pos x y z dx dy dz hball hvec⟩

end InfoGeometry.Canonical.BuresMetricClosedCartography

end noncomputable section
