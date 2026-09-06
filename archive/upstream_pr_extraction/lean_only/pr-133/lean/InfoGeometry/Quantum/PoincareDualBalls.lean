import Mathlib.Data.Complex.Basic
import Mathlib.Topology.Instances.Complex
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

namespace InfoGeometry.Quantum.PoincareDualBalls

open Complex

noncomputable section

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

def invTwinMap (z : ℂ) : ℂ := z⁻¹

theorem invTwinMap_involution (z : ℂ) :
    invTwinMap (invTwinMap z) = z := by
  unfold invTwinMap
  exact inv_inv z

theorem inner_outer_ball_duality (z : ℂ) (hz : z ≠ 0) :
    ‖z‖ < 1 ↔ 1 < ‖invTwinMap z‖ := by
  unfold invTwinMap
  rw [norm_inv]
  have hz_pos : 0 < ‖z‖ := norm_pos_iff.mpr hz
  rw [one_lt_inv_iff₀]
  exact (and_iff_right hz_pos).symm

theorem equator_invariance_under_inv (z : ℂ) :
    ‖z‖ = 1 ↔ ‖invTwinMap z‖ = 1 := by
  unfold invTwinMap
  rw [norm_inv]
  exact inv_eq_one.symm

theorem scale_inversion_fixed_point_confinement (σ : ℝ)
    (h : σ - 1 / 2 = -(σ - 1 / 2)) :
    σ = 1 / 2 := by
  linarith

theorem grand_poincare_dual_balls_synthesis (z : ℂ) (σ : ℝ) (hz : z ≠ 0)
    (h_symm : σ - 1 / 2 = -(σ - 1 / 2)) :
    (invTwinMap (invTwinMap z) = z) ∧
    (‖z‖ < 1 ↔ 1 < ‖invTwinMap z‖) ∧
    (‖z‖ = 1 ↔ ‖invTwinMap z‖ = 1) ∧
    (σ = 1 / 2) :=
  ⟨invTwinMap_involution z,
   inner_outer_ball_duality z hz,
   equator_invariance_under_inv z,
   scale_inversion_fixed_point_confinement σ h_symm⟩
