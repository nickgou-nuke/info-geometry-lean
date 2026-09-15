import InfoGeometry.Epistemology.NaturalGradientDissipation
import InfoGeometry.Canonical.LieFenchelQuadratic

open scoped Topology

noncomputable section

namespace InfoGeometry.Epistemology.QuadraticNaturalGradientFlow

open InfoGeometry.Convex
open HessianGeometry1D
open InfoGeometry.Epistemology.NaturalGradientDissipation
open Filter

def quadraticGeometry : HessianGeometry1D :=
  ⟨InfoGeometry.Canonical.LieFenchelQuadratic.psi⟩

theorem hasDerivAt_quadratic (point : ℝ) :
    HasDerivAt quadraticGeometry.potential point point := by
  change HasDerivAt (fun value : ℝ => (1 / 2 : ℝ) * ‖value‖ ^ 2) point point
  simp only [Real.norm_eq_abs, sq_abs]
  convert ((hasDerivAt_id point).pow 2).const_mul (1 / 2 : ℝ) using 1
  norm_num
  ring

theorem quadratic_dualMap : quadraticGeometry.dualMap = id := by
  funext point
  exact (hasDerivAt_quadratic point).deriv

theorem quadratic_metric (point : ℝ) : quadraticGeometry.metric point = 1 := by
  change deriv quadraticGeometry.dualMap point = 1
  rw [quadratic_dualMap]
  exact deriv_id point

theorem quadratic_divergence (point target : ℝ) :
    quadraticGeometry.divergence point target = (point - target) ^ 2 / 2 := by
  unfold divergence
  rw [quadratic_dualMap]
  have identity := InfoGeometry.Canonical.LieFenchelQuadratic.bregman_eq_half_norm_sub_sq point target
  simpa [InfoGeometry.Canonical.LieFenchelQuadratic.bregman, quadraticGeometry,
    Real.norm_eq_abs, sq_abs, div_eq_mul_inv, mul_comm] using identity

theorem quadratic_naturalVelocity (point target : ℝ) :
    naturalVelocity quadraticGeometry point target = -(point - target) := by
  simp only [naturalVelocity, divergenceGradient, quadratic_metric, quadratic_dualMap, id_eq, div_one]

theorem quadratic_dissipation_domination (point target : ℝ) :
    dissipation quadraticGeometry point target = 2 * quadraticGeometry.divergence point target := by
  rw [quadratic_divergence]
  simp only [dissipation, divergenceGradient, quadratic_metric, quadratic_dualMap, id_eq, div_one]
  ring

def trajectory (initial target time : ℝ) : ℝ :=
  target + (initial - target) * Real.exp (-time)

theorem trajectory_initial (initial target : ℝ) : trajectory initial target 0 = initial := by
  simp [trajectory]

theorem hasDerivAt_trajectory (initial target time : ℝ) :
    HasDerivAt (trajectory initial target)
      (naturalVelocity quadraticGeometry (trajectory initial target time) target) time := by
  rw [quadratic_naturalVelocity]
  convert ((((hasDerivAt_id time).neg).exp).const_mul (initial - target)).const_add target
    using 1
  simp [trajectory]

theorem trajectory_ne_target (initial target time : ℝ) (distinct : initial ≠ target) :
    trajectory initial target time ≠ target := by
  intro equal
  have nonzero : (initial - target) * Real.exp (-time) ≠ 0 :=
    mul_ne_zero (sub_ne_zero.mpr distinct) (Real.exp_ne_zero _)
  apply nonzero
  unfold trajectory at equal
  linarith

theorem divergence_exact_decay (initial target time : ℝ) :
    quadraticGeometry.divergence (trajectory initial target time) target =
      quadraticGeometry.divergence initial target * Real.exp (-2 * time) := by
  rw [quadratic_divergence, quadratic_divergence]
  simp only [trajectory, add_sub_cancel_left, mul_pow]
  rw [pow_two (Real.exp (-time)), ← Real.exp_add,
    show -time + -time = -2 * time by ring]
  ring

theorem trajectory_tendsto_target (initial target : ℝ) :
    Tendsto (trajectory initial target) atTop (𝓝 target) := by
  have limit := (Real.tendsto_exp_neg_atTop_nhds_zero.const_mul (initial - target)).const_add target
  simpa [trajectory] using limit

end InfoGeometry.Epistemology.QuadraticNaturalGradientFlow
