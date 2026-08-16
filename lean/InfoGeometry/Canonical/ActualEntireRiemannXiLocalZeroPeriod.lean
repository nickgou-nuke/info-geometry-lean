import InfoGeometry.Arithmetic.ActualRiemannXiEntireBridge
import InfoGeometry.Canonical.ActualEntireRiemannXiLogDerivativeCirclePeriodBridge
import InfoGeometry.Canonical.ActualEntireRiemannXiZeroFreeClosedForm

/-!
# Typed local zero data for the actual entire completed `riemannXi`

This owner packages the hypotheses needed by the existing local
factorization/contour kernel for the actual entire representative.  It proves
the normalized logarithmic circle-period readout from that data.  It does not
claim that every zero of `entireRiemannXi` has been globally classified or
that a local factorization witness has been constructed automatically.
-/

noncomputable section

namespace InfoGeometry.Canonical.ActualEntireRiemannXiLocalZeroPeriod

open Complex
open InfoGeometry.Arithmetic.ActualRiemannXiEntireBridge
open InfoGeometry.Canonical.ActualEntireRiemannXiLogDerivativeBridge
open InfoGeometry.Canonical.ActualEntireRiemannXiLogDerivativeCirclePeriodBridge
open InfoGeometry.Canonical.ActualEntireRiemannXiZeroFreeClosedForm
open InfoGeometry.Canonical.ZetaLogarithmicPoleCirclePeriod

structure Datum where
  rho : ℂ
  m : ℕ
  m_pos : 0 < m
  radius : ℝ
  radius_pos : 0 < radius
  g : ℂ → ℂ
  h : ℂ → ℂ
  factorization :
    entireRiemannXi = fun z => (z - rho) ^ m * g z
  g_differentiable :
    DifferentiableOn ℂ g (Metric.closedBall rho radius)
  h_differentiable :
    DifferentiableOn ℂ h (Metric.closedBall rho radius)
  g_deriv : ∀ z, HasDerivAt g (h z) z
  g_ne_zero : ∀ z, g z ≠ 0
  pole_integrable :
    CircleIntegrable
      (ZetaLogarithmicPoleCirclePeriod.logarithmicPole rho (m : ℤ))
      rho radius
  correction_integrable :
    CircleIntegrable (fun z => h z / g z) rho radius

theorem normalized_logDifferential_circleIntegral (D : Datum) :
    (2 * Real.pi * Complex.I : ℂ)⁻¹ *
        (∮ z in C(D.rho, D.radius),
          entireRiemannXiLogDifferential z) =
      - (D.m : ℂ) := by
  exact entireRiemannXi_normalized_logDifferential_circleIntegral_of_factorization
    D.rho D.m D.g D.h D.radius_pos D.m_pos D.factorization
    D.g_differentiable D.h_differentiable D.g_deriv D.g_ne_zero
    D.pole_integrable D.correction_integrable

theorem normalized_actual_form_unit_circleIntegral (D : Datum) :
    (2 * Real.pi * Complex.I : ℂ)⁻¹ *
        (∮ z in C(D.rho, D.radius),
          actual.form z (fun _ : Fin 1 => (1 : ℂ))) =
      - (D.m : ℂ) := by
  have hreadout :
      (fun z : ℂ => actual.form z (fun _ : Fin 1 => (1 : ℂ))) =
        entireRiemannXiLogDifferential := by
    funext z
    simp
  rw [hreadout]
  exact normalized_logDifferential_circleIntegral D

theorem normalized_logDifferential_circleIntegral_integer_readout
    (D : Datum) :
    ∃ k : ℤ,
      (2 * Real.pi * Complex.I : ℂ)⁻¹ *
          (∮ z in C(D.rho, D.radius),
            entireRiemannXiLogDifferential z) =
        (k : ℂ) := by
  refine ⟨-(D.m : ℤ), ?_⟩
  rw [normalized_logDifferential_circleIntegral D]
  norm_num

end InfoGeometry.Canonical.ActualEntireRiemannXiLocalZeroPeriod
