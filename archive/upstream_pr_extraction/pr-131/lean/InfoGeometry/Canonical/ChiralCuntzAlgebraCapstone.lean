import InfoGeometry.Algebra.ChiralCuntzAlgebra

namespace InfoGeometry.Canonical.ChiralCuntzAlgebraCapstone

open InfoGeometry.Algebra.ChiralCuntzAlgebra

theorem capstone_chiral_cuntz_algebra_synthesis
    (θ ξ N_L N_R β : ℝ) (p : ℕ) :
    (leftNullHop N_L N_R = N_L) ∧
    (rightNullHop N_L N_R = N_R) ∧
    (2 * chiralShiftGenerator N_L N_R = N_L - N_R) ∧
    (2 * chiralTiltGenerator N_L N_R = N_L + N_R) ∧
    (‖chiralShiftOperator θ N_L N_R‖ = 1) ∧
    (chiralTiltOperator 0 N_L N_R = 1) ∧
    (bostConnesKMSOperator p 0 β = 1) :=
  grand_chiral_cuntz_algebra_synthesis θ ξ N_L N_R β p

end InfoGeometry.Canonical.ChiralCuntzAlgebraCapstone
