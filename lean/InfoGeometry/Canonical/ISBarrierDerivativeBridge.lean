/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.ScalarLogBarrier
import InfoGeometry.Canonical.SelfConcordantLogGeneratingLyapunov

/-! Actual derivatives of the existing IS kernel and dissipation along a supplied
trajectory. This does not assert existence or convergence of that trajectory. -/
noncomputable section
namespace InfoGeometry.Canonical.SelfConcordantZetaBarrier

theorem hasDerivAt_isBarrierKernel {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt isBarrierKernel (isBarrierKernel_deriv x) x := by
  change HasDerivAt (fun y : ℝ => y - Real.log y - 1) (1 - 1 / x) x
  simpa [isBarrierKernel, isBarrierKernel_deriv, ScalarLogBarrier.barrier,
    ScalarLogBarrier.gradient, one_div, sub_eq_add_neg] using
    ((hasDerivAt_id x).add (ScalarLogBarrier.hasDerivAt_barrier hx)).sub_const 1

theorem hasDerivAt_isBarrierKernel_deriv {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt isBarrierKernel_deriv (isBarrierKernel_deriv2 x) x := by
  change HasDerivAt (fun y : ℝ => 1 - 1 / y) (1 / x ^ 2) x
  simpa [isBarrierKernel_deriv, isBarrierKernel_deriv2, ScalarLogBarrier.gradient,
    ScalarLogBarrier.hessian, one_div, sub_eq_add_neg] using
    (ScalarLogBarrier.hasDerivAt_gradient hx).const_add 1

theorem hasDerivAt_isBarrierKernel_deriv2 {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt isBarrierKernel_deriv2 (isBarrierKernel_deriv3 x) x := by
  change HasDerivAt (fun y : ℝ => 1 / y ^ 2) (-2 / x ^ 3) x
  have h := ScalarLogBarrier.hasDerivAt_hessian hx
  change HasDerivAt (fun y : ℝ => (y ^ 2)⁻¹) (-2 * (x ^ 3)⁻¹) x at h
  simpa [isBarrierKernel_deriv2, isBarrierKernel_deriv3, ScalarLogBarrier.hessian,
    ScalarLogBarrier.thirdDerivative, div_eq_mul_inv] using
    h

end InfoGeometry.Canonical.SelfConcordantZetaBarrier

namespace InfoGeometry.Canonical.SelfConcordantLogGeneratingLyapunov
open SelfConcordantZetaBarrier

theorem hasDerivAt_potential_along_field {κ t : ℝ} {γ : ℝ → ℝ}
    (hx : γ t ≠ 0) (hγ : HasDerivAt γ (naturalGradientField κ (γ t)) t) :
    HasDerivAt (fun s => lyapunovPotential (γ s)) (-κ * (γ t - 1) ^ 2) t := by
  have h := (hasDerivAt_isBarrierKernel hx).comp t hγ
  change HasDerivAt (fun s => lyapunovPotential (γ s))
    (lyapunovLieDerivative κ (γ t)) t at h
  rw [lyapunovLieDerivative_eq κ (γ t) hx] at h
  exact h

theorem deriv_potential_along_field_nonpos {κ t : ℝ} {γ : ℝ → ℝ}
    (hκ : 0 ≤ κ) (hx : γ t ≠ 0)
    (hγ : HasDerivAt γ (naturalGradientField κ (γ t)) t) :
    deriv (fun s => lyapunovPotential (γ s)) t ≤ 0 := by
  rw [(hasDerivAt_potential_along_field hx hγ).deriv]
  exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hκ) (sq_nonneg _)

theorem deriv_potential_along_field_neg {κ t : ℝ} {γ : ℝ → ℝ}
    (hκ : 0 < κ) (hx : γ t ≠ 0) (hne : γ t ≠ 1)
    (hγ : HasDerivAt γ (naturalGradientField κ (γ t)) t) :
    deriv (fun s => lyapunovPotential (γ s)) t < 0 := by
  rw [(hasDerivAt_potential_along_field hx hγ).deriv]
  exact mul_neg_of_neg_of_pos (neg_neg_of_pos hκ)
    (sq_pos_of_ne_zero (sub_ne_zero.mpr hne))

end InfoGeometry.Canonical.SelfConcordantLogGeneratingLyapunov
