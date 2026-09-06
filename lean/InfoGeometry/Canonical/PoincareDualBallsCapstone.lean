import InfoGeometry.Quantum.PoincareDualBalls

namespace InfoGeometry.Canonical.PoincareDualBallsCapstone

open InfoGeometry.Quantum.PoincareDualBalls

theorem capstone_poincare_dual_balls_synthesis (z : ℂ) (σ : ℝ) (hz : z ≠ 0)
    (h_symm : σ - 1 / 2 = -(σ - 1 / 2)) :
    (invTwinMap (invTwinMap z) = z) ∧
    (‖z‖ < 1 ↔ 1 < ‖invTwinMap z‖) ∧
    (‖z‖ = 1 ↔ ‖invTwinMap z‖ = 1) ∧
    (σ = 1 / 2) := by
  exact ⟨invTwinMap_involution z,
    inner_outer_ball_duality z hz,
    equator_invariance_under_inv z,
    scale_inversion_fixed_point_confinement σ h_symm⟩

end InfoGeometry.Canonical.PoincareDualBallsCapstone
