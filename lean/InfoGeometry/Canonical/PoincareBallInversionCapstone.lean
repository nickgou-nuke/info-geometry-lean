import InfoGeometry.Quantum.PoincareBallInversion
import InfoGeometry.Algebra.FiniteSpinAlgebra

namespace InfoGeometry.Canonical.PoincareBallInversionCapstone

open InfoGeometry.Quantum.PoincareBallInversion

theorem capstone_poincare_ball_inversion_synthesis (r σ : ℝ) (hr : 0 < r)
    (h_inv : poincareInversion (Real.exp (σ - 1 / 2)) =
      Real.exp (σ - 1 / 2)) :
    (poincareInversion (poincareInversion r) = r) ∧
    (rapidityScale (poincareInversion r) = - rapidityScale r) ∧
    (poincareInversion 1 = 1) ∧
    (poincareInversion r = r ↔ r = 1) ∧
    (σ = 1 / 2) := by
  exact ⟨poincare_inversion_involution r (ne_of_gt hr),
    poincare_inversion_rapidity_neg r hr,
    poincare_equator_fixed_point,
    poincare_inversion_fixed_iff r hr,
    poincare_inner_outer_critical_line σ h_inv⟩

end InfoGeometry.Canonical.PoincareBallInversionCapstone
