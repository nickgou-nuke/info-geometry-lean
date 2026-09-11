import InfoGeometry.Canonical.ActualEntireRiemannXiDifferentialFormBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.ActualEntireRiemannXiLocalZeroPeriod
import InfoGeometry.Canonical.ActualEntireRiemannXiLogDerivativeCirclePeriodBridge

/-!
# Period readback of the actual entire `xi` one-form

The local zero-period owner integrates the scalar logarithmic coefficient.
This file identifies that coefficient with evaluation of the native Mathlib
degree-one differential form on the unit tangent.  It introduces no global
zero classification or de Rham cohomology class.
-/

noncomputable section

namespace InfoGeometry.Canonical.ActualEntireRiemannXiOneFormPeriodBridge

open InfoGeometry.Arithmetic.ActualRiemannXiEntireBridge
open InfoGeometry.Canonical.ActualEntireRiemannXiDifferentialFormBridge
open InfoGeometry.Canonical.ActualEntireRiemannXiLogDerivativeBridge
open InfoGeometry.Canonical.ActualEntireRiemannXiLogDerivativeCirclePeriodBridge
open InfoGeometry.Canonical.ActualEntireRiemannXiLocalZeroPeriod
open InfoGeometry.Canonical.ActualEntireRiemannXiZeroFreeLocus
open InfoGeometry.Canonical.ActualEntireRiemannXiZeroFreeLogDifferential

theorem entireRiemannXiLogDifferentialForm_unit_tangent (s : ℂ) :
    entireRiemannXiLogDifferentialForm s (fun _ => (1 : ℂ)) =
      entireRiemannXiLogDifferential s := by
  rw [entireRiemannXiLogDifferentialForm_eq_scalarComplexOneForm,
    scalarComplexOneForm_apply]
  simp

theorem entireRiemannXiLogDifferentialForm_unit_tangent_circleIntegrable_of_closedBall_subset_zero_free
    (rho : ℂ) {R : ℝ} (hR : 0 ≤ R)
    (hball : Metric.closedBall rho R ⊆ entireRiemannXiZeroFreeLocus) :
    CircleIntegrable
      (fun z => entireRiemannXiLogDifferentialForm z
        (fun _ : Fin 1 => (1 : ℂ))) rho R := by
  have hreadout :
      (fun z : ℂ => entireRiemannXiLogDifferentialForm z
        (fun _ : Fin 1 => (1 : ℂ))) =
        entireRiemannXiLogDifferential := by
    funext z
    exact entireRiemannXiLogDifferentialForm_unit_tangent z
  rw [hreadout]
  exact entireRiemannXiLogDifferential_circleIntegrable_of_closedBall_subset_zero_free
    rho hR hball

theorem entireRiemannXiLogDifferentialForm_unit_tangent_circleIntegral_eq_zero_of_closedBall_subset_zero_free
    (rho : ℂ) {R : ℝ} (hR : 0 < R)
    (hball : Metric.closedBall rho R ⊆ entireRiemannXiZeroFreeLocus) :
    (∮ z in C(rho, R),
      entireRiemannXiLogDifferentialForm z
        (fun _ : Fin 1 => (1 : ℂ))) = 0 := by
  have hreadout :
      (fun z : ℂ => entireRiemannXiLogDifferentialForm z
        (fun _ : Fin 1 => (1 : ℂ))) =
        entireRiemannXiLogDifferential := by
    funext z
    exact entireRiemannXiLogDifferentialForm_unit_tangent z
  rw [hreadout]
  exact entireRiemannXi_logDerivative_circleIntegral_eq_zero_of_nonvanishing
    rho hR hball

theorem entireRiemannXiLogDifferentialForm_circleIntegral_eq_zero_of_re_lt_zero
    (rho : ℂ) {R : ℝ} (hR : 0 < R)
    (hRe : ∀ z ∈ Metric.closedBall rho R, z.re < 0) :
    (∮ z in C(rho, R),
      entireRiemannXiLogDifferentialForm z (fun _ : Fin 1 => (1 : ℂ))) = 0 := by
  have hcoeff :
      (fun z : ℂ =>
        entireRiemannXiLogDifferentialForm z (fun _ : Fin 1 => (1 : ℂ))) =
        entireRiemannXiLogDifferential := by
    funext z
    exact entireRiemannXiLogDifferentialForm_unit_tangent z
  rw [hcoeff]
  simpa only [entireRiemannXiLogDifferential_eq] using
    (entireRiemannXi_logDerivative_circleIntegral_eq_zero_of_re_lt_zero
      rho hR hRe)

theorem normalized_entireRiemannXiLogDifferentialForm_circleIntegral
    (D : Datum) :
    (2 * Real.pi * Complex.I : ℂ)⁻¹ *
        (∮ z in C(D.rho, D.radius),
          entireRiemannXiLogDifferentialForm z (fun _ => (1 : ℂ))) =
      - (D.m : ℂ) := by
  have hcoeff :
      (fun z : ℂ =>
        entireRiemannXiLogDifferentialForm z (fun _ => (1 : ℂ))) =
        entireRiemannXiLogDifferential := by
    funext z
    exact entireRiemannXiLogDifferentialForm_unit_tangent z
  rw [hcoeff]
  exact normalized_logDifferential_circleIntegral D

end InfoGeometry.Canonical.ActualEntireRiemannXiOneFormPeriodBridge
