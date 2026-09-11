import InfoGeometry.Arithmetic.ActualRiemannXiEntireBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra
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

structure DatumData where
  rho : ℂ
  m : ℕ
  radius : ℝ
  g : ℂ → ℂ
  h : ℂ → ℂ

def DatumValid (D : DatumData) : Prop :=
  0 < D.m ∧
  0 < D.radius ∧
  (entireRiemannXi = fun z => (z - D.rho) ^ D.m * D.g z) ∧
  DifferentiableOn ℂ D.g (Metric.closedBall D.rho D.radius) ∧
  DifferentiableOn ℂ D.h (Metric.closedBall D.rho D.radius) ∧
  (∀ z, HasDerivAt D.g (D.h z) z) ∧
  (∀ z, D.g z ≠ 0) ∧
  CircleIntegrable
    (ZetaLogarithmicPoleCirclePeriod.logarithmicPole D.rho (D.m : ℤ))
    D.rho D.radius ∧
  CircleIntegrable (fun z => D.h z / D.g z) D.rho D.radius

def Datum := {D : DatumData // DatumValid D}

namespace Datum

abbrev rho (D : Datum) := D.1.rho
abbrev m (D : Datum) := D.1.m
abbrev radius (D : Datum) := D.1.radius
abbrev g (D : Datum) := D.1.g
abbrev h (D : Datum) := D.1.h
abbrev m_pos (D : Datum) : 0 < D.m := D.2.1
abbrev radius_pos (D : Datum) : 0 < D.radius := D.2.2.1
abbrev factorization (D : Datum) :
    entireRiemannXi = fun z => (z - D.rho) ^ D.m * D.g z := D.2.2.2.1
abbrev g_differentiable (D : Datum) :
    DifferentiableOn ℂ D.g (Metric.closedBall D.rho D.radius) := D.2.2.2.2.1
abbrev h_differentiable (D : Datum) :
    DifferentiableOn ℂ D.h (Metric.closedBall D.rho D.radius) := D.2.2.2.2.2.1
abbrev g_deriv (D : Datum) : ∀ z, HasDerivAt D.g (D.h z) z := D.2.2.2.2.2.2.1
abbrev g_ne_zero (D : Datum) : ∀ z, D.g z ≠ 0 := D.2.2.2.2.2.2.2.1
abbrev pole_integrable (D : Datum) :
    CircleIntegrable
      (ZetaLogarithmicPoleCirclePeriod.logarithmicPole D.rho (D.m : ℤ))
      D.rho D.radius := D.2.2.2.2.2.2.2.2.1
abbrev correction_integrable (D : Datum) :
    CircleIntegrable (fun z => D.h z / D.g z) D.rho D.radius := D.2.2.2.2.2.2.2.2.2

end Datum

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
