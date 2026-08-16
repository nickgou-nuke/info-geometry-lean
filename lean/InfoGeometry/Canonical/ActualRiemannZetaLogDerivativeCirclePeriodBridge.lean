import InfoGeometry.Arithmetic.ActualRiemannZetaVonMangoldtBridge
import InfoGeometry.Canonical.ZetaLogarithmicPoleCirclePeriod

/-!
# Local logarithmic period for the actual Riemann zeta function

This owner specializes the repository's zero-free circle-integral kernel to
Mathlib's `riemannZeta`.  Regularity and nonvanishing on the disk remain
explicit hypotheses; no analytic continuation or zero classification is
silently introduced.
-/

noncomputable section

open scoped Topology

namespace InfoGeometry.Canonical.ActualRiemannZetaLogDerivativeCirclePeriodBridge

open Complex
open InfoGeometry.Arithmetic.ActualRiemannZetaVonMangoldtBridge
open InfoGeometry.Canonical.ZetaLogarithmicPoleCirclePeriod

theorem actualRiemannZeta_logDerivative_circleIntegral_eq_zero_of_nonvanishing
    (rho : ℂ) {R : ℝ} (hR : 0 < R)
    (hζ : DifferentiableOn ℂ riemannZeta (Metric.closedBall rho R))
    (hderiv : DifferentiableOn ℂ (deriv riemannZeta)
      (Metric.closedBall rho R))
    (hzero : ∀ z ∈ Metric.closedBall rho R, riemannZeta z ≠ 0) :
    (∮ z in C(rho, R),
      actualRiemannZetaLogDerivative z) = 0 := by
  have hquot := circleIntegral_div_eq_zero_of_differentiableOn_nonzero
    rho riemannZeta (deriv riemannZeta) hR.le hζ hderiv hzero
  calc
    (∮ z in C(rho, R), actualRiemannZetaLogDerivative z) =
        (-1 : ℂ) •
          (∮ z in C(rho, R), deriv riemannZeta z / riemannZeta z) := by
      rw [← circleIntegral.integral_smul]
      congr 1
      funext z
      simp [actualRiemannZetaLogDerivative, neg_div]
    _ = 0 := by
      rw [hquot]
      simp

theorem actualRiemannZeta_normalized_logDerivative_circleIntegral_eq_zero_of_nonvanishing
    (rho : ℂ) {R : ℝ} (hR : 0 < R)
    (hζ : DifferentiableOn ℂ riemannZeta (Metric.closedBall rho R))
    (hderiv : DifferentiableOn ℂ (deriv riemannZeta)
      (Metric.closedBall rho R))
    (hzero : ∀ z ∈ Metric.closedBall rho R, riemannZeta z ≠ 0) :
    (2 * Real.pi * Complex.I : ℂ)⁻¹ *
        (∮ z in C(rho, R), actualRiemannZetaLogDerivative z) = 0 := by
  rw [actualRiemannZeta_logDerivative_circleIntegral_eq_zero_of_nonvanishing
    rho hR hζ hderiv hzero]
  simp

theorem actualRiemannZeta_normalized_logDerivative_circleIntegral_eq_zero_of_one_lt_re
    (rho : ℂ) {R : ℝ} (hR : 0 < R)
    (hRe : ∀ z ∈ Metric.closedBall rho R, 1 < z.re) :
    (2 * Real.pi * Complex.I : ℂ)⁻¹ *
        (∮ z in C(rho, R), actualRiemannZetaLogDerivative z) = 0 := by
  let U : Set ℂ := {z : ℂ | 1 < z.re}
  have hUopen : IsOpen U := by
    exact isOpen_lt continuous_const Complex.continuous_re
  have hζU : DifferentiableOn ℂ riemannZeta U := by
    intro z hz
    change 1 < z.re at hz
    apply DifferentiableAt.differentiableWithinAt
    apply differentiableAt_riemannZeta
    show z ≠ (1 : ℂ)
    intro hz1
    rw [hz1] at hz
    norm_num at hz
  have hsubset : Metric.closedBall rho R ⊆ U := by
    intro z hz
    exact hRe z hz
  have hζ : DifferentiableOn ℂ riemannZeta (Metric.closedBall rho R) :=
    hζU.mono hsubset
  have hderiv : DifferentiableOn ℂ (deriv riemannZeta)
      (Metric.closedBall rho R) :=
    (hζU.deriv hUopen).mono hsubset
  have hzero : ∀ z ∈ Metric.closedBall rho R, riemannZeta z ≠ 0 := by
    intro z hz
    exact riemannZeta_ne_zero_of_one_lt_re (hRe z hz)
  exact actualRiemannZeta_normalized_logDerivative_circleIntegral_eq_zero_of_nonvanishing
    rho hR hζ hderiv hzero

end InfoGeometry.Canonical.ActualRiemannZetaLogDerivativeCirclePeriodBridge
