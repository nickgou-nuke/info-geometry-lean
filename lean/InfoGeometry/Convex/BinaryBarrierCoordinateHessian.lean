import InfoGeometry.Convex.BipolarLogitBarrierDuality
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Analysis.LogOddsSimplexGeometry

/-!
# Binary barrier Hessian under a nonlinear log-odds chart

Reuse the interval-barrier owner and the actual logistic trajectory.
The Hessian of a composite scalar potential differs from the pullback of
the original Hessian metric by a gradient-times-acceleration term.
These results do not identify the Hessian with a modular Hamiltonian.
-/

noncomputable section
namespace InfoGeometry.Convex.BinaryBarrierCoordinateHessian

open InfoGeometry.Convex.BipolarLogitBarrierDuality
open InfoGeometry.Analysis.LogOddsSimplexGeometry

/-- The existing binary barrier becomes log(4) plus twice log(cosh). -/
theorem interval_barrier_log_cosh (ξ : ℝ) :
    intervalBarrier (trajectory 1 0 ξ) = Real.log 4 + 2 * Real.log (Real.cosh ξ) := by
  have he : Real.exp (2 * ξ) = Real.exp ξ * Real.exp ξ := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hs : 1 + Real.exp (2 * ξ) = (2 * Real.cosh ξ) * Real.exp ξ := by
    rw [Real.cosh_eq, Real.exp_neg, he]
    field_simp
    ring
  have h4 : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  change intervalBarrier (InfoGeometry.Analysis.BipolarCrossRatioLog.logistic
    (2 * (1 * ξ + 0))) = _
  simp only [one_mul, add_zero]
  rw [intervalBarrier_logistic, hs,
    Real.log_mul (mul_ne_zero (by norm_num) (Real.cosh_pos ξ).ne') (Real.exp_ne_zero ξ),
    Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (Real.cosh_pos ξ).ne', Real.log_exp, h4]
  ring

/-- First derivative of the existing barrier along a unit-speed half-logit chart. -/
theorem barrier_chart_hasDerivAt (ξ : ℝ) :
    HasDerivAt (fun t => intervalBarrier (trajectory 1 0 t))
      (4 * trajectory 1 0 ξ - 2) ξ := by
  have hp := trajectory_mem_Ioo 1 0 ξ
  have h := (hasDerivAt_intervalBarrier hp.1 hp.2).comp ξ
    (hasDerivAt_trajectory 1 0 ξ)
  convert h using 1
  unfold intervalBarrierGradient
  field_simp [hp.1.ne', (sub_pos.mpr hp.2).ne']
  ring

/-- Second derivative computed from the actual first derivative. -/
theorem barrier_chart_second_derivative (ξ : ℝ) :
    deriv (deriv (fun t => intervalBarrier (trajectory 1 0 t))) ξ =
      8 * trajectory 1 0 ξ * (1 - trajectory 1 0 ξ) := by
  have hf : deriv (fun t => intervalBarrier (trajectory 1 0 t)) =
      fun t => 4 * trajectory 1 0 t - 2 := by
    funext t
    exact (barrier_chart_hasDerivAt t).deriv
  rw [hf, (((hasDerivAt_trajectory 1 0 ξ).const_mul 4).sub_const 2).deriv]
  ring

/-- Pullback of the original Hessian quadratic form in the same chart. -/
theorem barrier_hessian_pullback (ξ : ℝ) :
    intervalBarrierHessian (trajectory 1 0 ξ) * (deriv (trajectory 1 0) ξ) ^ 2 =
      4 * ((trajectory 1 0 ξ) ^ 2 + (1 - trajectory 1 0 ξ) ^ 2) := by
  have hp := trajectory_mem_Ioo 1 0 ξ
  rw [(hasDerivAt_trajectory 1 0 ξ).deriv]
  unfold intervalBarrierHessian
  field_simp [hp.1.ne', (sub_pos.mpr hp.2).ne']
  ring

/-- The correction is nonpositive and vanishes only at the midpoint. -/
theorem barrier_hessian_coordinate_defect (ξ : ℝ) :
    deriv (deriv (fun t => intervalBarrier (trajectory 1 0 t))) ξ -
      intervalBarrierHessian (trajectory 1 0 ξ) * (deriv (trajectory 1 0) ξ) ^ 2 =
      -4 * (2 * trajectory 1 0 ξ - 1) ^ 2 := by
  rw [barrier_chart_second_derivative, barrier_hessian_pullback]
  ring

/-- Native second-order chain rule, with the correction evaluated explicitly. -/
theorem barrier_second_order_chain_rule (ξ : ℝ) :
    deriv (deriv (fun t => intervalBarrier (trajectory 1 0 t))) ξ =
      intervalBarrierHessian (trajectory 1 0 ξ) * (deriv (trajectory 1 0) ξ) ^ 2 +
      intervalBarrierGradient (trajectory 1 0 ξ) * deriv (deriv (trajectory 1 0)) ξ := by
  have hp := trajectory_mem_Ioo 1 0 ξ
  rw [barrier_chart_second_derivative, barrier_hessian_pullback, trajectory_acceleration]
  unfold intervalBarrierGradient
  field_simp [hp.1.ne', (sub_pos.mpr hp.2).ne']
  ring

theorem barrier_chart_hessian_le_pullback (ξ : ℝ) :
    deriv (deriv (fun t => intervalBarrier (trajectory 1 0 t))) ξ ≤
      intervalBarrierHessian (trajectory 1 0 ξ) * (deriv (trajectory 1 0) ξ) ^ 2 := by
  have h := barrier_hessian_coordinate_defect ξ
  nlinarith [sq_nonneg (2 * trajectory 1 0 ξ - 1)]

theorem barrier_chart_third_derivative (ξ : ℝ) :
    deriv (deriv (deriv (fun t => intervalBarrier (trajectory 1 0 t)))) ξ =
      16 * trajectory 1 0 ξ * (1 - trajectory 1 0 ξ) * (1 - 2 * trajectory 1 0 ξ) := by
  have hf : deriv (deriv (fun t => intervalBarrier (trajectory 1 0 t))) =
      fun t => 8 * trajectory 1 0 t * (1 - trajectory 1 0 t) := by
    funext t
    exact barrier_chart_second_derivative t
  rw [hf]
  have hd := hasDerivAt_trajectory 1 0 ξ
  have h := (hd.const_mul 8).mul ((hasDerivAt_const ξ (1 : ℝ)).sub hd)
  change HasDerivAt (fun t => 8 * trajectory 1 0 t * (1 - trajectory 1 0 t)) _ ξ at h
  rw [h.deriv]
  dsimp
  ring

/-- A concrete violation of the squared standard self-concordance inequality.
Nonlinear coordinate changes do not preserve that affine-coordinate property. -/
theorem transformed_barrier_self_concordance_counterexample :
    ∃ ξ : ℝ,
      4 * (deriv (deriv (fun t => intervalBarrier (trajectory 1 0 t))) ξ) ^ 3 <
        (deriv (deriv (deriv (fun t => intervalBarrier (trajectory 1 0 t)))) ξ) ^ 2 := by
  let ξ : ℝ := InfoGeometry.Canonical.AmariBinarySimplexBridge.logit (15 / 16) / 2
  have ht : trajectory 1 0 ξ = 15 / 16 := by
    unfold trajectory
    have harg : 2 * (1 * ξ + 0) =
        InfoGeometry.Canonical.AmariBinarySimplexBridge.logit (15 / 16) := by
      dsimp [ξ]
      ring
    rw [harg]
    exact InfoGeometry.Canonical.AmariBinarySimplexBridge.logistic_logit
      (by constructor <;> norm_num)
  refine ⟨ξ, ?_⟩
  rw [barrier_chart_second_derivative, barrier_chart_third_derivative, ht]
  norm_num

end InfoGeometry.Convex.BinaryBarrierCoordinateHessian
