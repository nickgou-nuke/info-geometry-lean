import InfoGeometry.Quantum.BaxterTQRelation
import InfoGeometry.Algebra.FiniteSpinAlgebra

namespace InfoGeometry.Canonical.BaxterTQRelationCapstone

open InfoGeometry.Quantum.BaxterTQRelation

theorem capstone_baxter_TQ_synthesis (Γ u η : ℝ) :
    (baxterQShiftForward Γ u η = ((Real.exp (- (Γ / 2 * η)) : ℝ) : ℂ) * baxterQFunction Γ u) ∧
    (baxterQShiftBackward Γ u η = ((Real.exp ((Γ / 2 * η)) : ℝ) : ℂ) * baxterQFunction Γ u) ∧
    (‖baxterQFunction Γ u‖ = 1) ∧
    (baxterTransferEigenvalue Γ η * baxterQFunction Γ u =
     baxterQShiftForward Γ u η + baxterQShiftBackward Γ u η) := by
  exact ⟨baxter_Q_shift_forward_eq Γ u η,
    baxter_Q_shift_backward_eq Γ u η,
    baxter_Q_unitary Γ u,
    baxter_TQ_exact_relation Γ u η⟩

end InfoGeometry.Canonical.BaxterTQRelationCapstone
