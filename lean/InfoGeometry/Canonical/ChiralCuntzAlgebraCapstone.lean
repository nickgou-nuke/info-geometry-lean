import InfoGeometry.Algebra.ChiralCuntzAlgebra

namespace InfoGeometry.Canonical.ChiralCuntzAlgebraCapstone

open InfoGeometry.Algebra.ChiralCuntzAlgebra

/-! The capstone is assembled from the independent finite carrier laws. -/
theorem capstone_chiral_cuntz_algebra_synthesis
    (θ ξ N_L N_R β : ℝ) (p : ℕ) :
    (leftNullHop N_L N_R = N_L) ∧
    (rightNullHop N_L N_R = N_R) ∧
    (2 * chiralShiftGenerator N_L N_R = N_L - N_R) ∧
    (2 * chiralTiltGenerator N_L N_R = N_L + N_R) ∧
    (‖chiralShiftOperator θ N_L N_R‖ = 1) ∧
    (chiralTiltOperator 0 N_L N_R = 1) ∧
    (bostConnesKMSOperator p 0 β = 1) := by
  exact ⟨left_null_hop_eq_N_L N_L N_R,
    right_null_hop_eq_N_R N_L N_R,
    shift_generator_diff N_L N_R,
    tilt_generator_sum N_L N_R,
    chiral_shift_operator_unitary θ N_L N_R,
    chiral_tilt_vacuum_at_critical_equator N_L N_R,
    bost_connes_kms_vacuum p β⟩

end InfoGeometry.Canonical.ChiralCuntzAlgebraCapstone
