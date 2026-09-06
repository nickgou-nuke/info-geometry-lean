import InfoGeometry.Quantum.PoincareBallInversion

namespace InfoGeometry.Canonical.PoincareBallInversionCapstone

open InfoGeometry.Quantum.PoincareBallInversion

theorem capstone_poincare_ball_inversion_synthesis (r σ : ℝ) (hr : 0 < r)
    (h_inv : poincareInversion (Real.exp (σ - 1/2)) = Real.exp (σ - 1/2)) :
    (poincareInversion (poincareInversion r) = r) ∧
    (rapidityScale (poincareInversion r) = - rapidityScale r) ∧
    (poincareInversion 1 = 1) ∧
    (poincareInversion r = r ↔ r = 1) ∧
    (σ = 1 / 2) :=
  grand_poincare_ball_inversion_synthesis r σ hr h_inv

end InfoGeometry.Canonical.PoincareBallInversionCapstone
