import InfoGeometry.Arithmetic.ActualRiemannXiEntireBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Arithmetic.ActualRiemannXiRegularityBridge
import InfoGeometry.Canonical.ActualEntireRiemannXiLogDerivativeBridge
import InfoGeometry.Canonical.LogDerivativeLocalFactorizationBridge
import InfoGeometry.Canonical.ActualEntireRiemannXiZeroFreeLocus

/-!
# Local period readout for the entire completed Riemann xi

This is the entire-function counterpart of the regular `riemannXi` circle
period owner.  The contour calculation is inherited from the generic local
factorization theorem.  The local factorization, multiplicity, and
nonvanishing data remain explicit; no global zero divisor or de Rham class is
constructed here.
-/

noncomputable section

namespace InfoGeometry.Canonical.ActualEntireRiemannXiLogDerivativeCirclePeriodBridge

open Complex
open InfoGeometry.Arithmetic.ActualRiemannXiEntireBridge
open InfoGeometry.Arithmetic.ActualRiemannXiRegularityBridge
open InfoGeometry.Canonical.ActualEntireRiemannXiLogDerivativeBridge
open InfoGeometry.Canonical.LogDerivativeLocalFactorizationBridge
open InfoGeometry.Canonical.ActualEntireRiemannXiZeroFreeLocus
open InfoGeometry.Canonical.ZetaLogarithmicPoleCirclePeriod

theorem entireRiemannXi_normalized_logDerivative_circleIntegral_of_factorization
    (rho : ℂ) (m : ℕ) (g h : ℂ → ℂ) {R : ℝ} (hR : 0 < R)
    (hm : 0 < m)
    (hfactor : entireRiemannXi = fun z => (z - rho) ^ m * g z)
    (hg : DifferentiableOn ℂ g (Metric.closedBall rho R))
    (hh : DifferentiableOn ℂ h (Metric.closedBall rho R))
    (hg_deriv : ∀ z, HasDerivAt g (h z) z)
    (hg0 : ∀ z, g z ≠ 0)
    (hpole : CircleIntegrable
      (ZetaLogarithmicPoleCirclePeriod.logarithmicPole rho (m : ℤ)) rho R)
    (hcorr : CircleIntegrable (fun z => h z / g z) rho R) :
    (2 * Real.pi * Complex.I : ℂ)⁻¹ *
        (∮ z in C(rho, R), -(deriv entireRiemannXi z / entireRiemannXi z)) =
      - (m : ℂ) := by
  exact normalized_logDerivative_circleIntegral_eq_neg_natCast
    rho m entireRiemannXi g h hR hm hfactor hg hh hg_deriv hg0 hpole hcorr

theorem entireRiemannXi_normalized_logDerivative_circleIntegral_of_factorization_derived
    (rho : ℂ) (m : ℕ) (g h : ℂ → ℂ) {R : ℝ} (hR : 0 < R)
    (hm : 0 < m)
    (hfactor : entireRiemannXi = fun z => (z - rho) ^ m * g z)
    (hg : DifferentiableOn ℂ g (Metric.closedBall rho R))
    (hh : DifferentiableOn ℂ h (Metric.closedBall rho R))
    (hg_deriv : ∀ z, HasDerivAt g (h z) z)
    (hg0 : ∀ z, g z ≠ 0) :
    (2 * Real.pi * Complex.I : ℂ)⁻¹ *
        (∮ z in C(rho, R),
          -(deriv entireRiemannXi z / entireRiemannXi z)) =
      - (m : ℂ) := by
  exact normalized_logDerivative_circleIntegral_eq_neg_natCast_derived
    rho m entireRiemannXi g h hR hm hfactor hg hh hg_deriv hg0

theorem entireRiemannXi_normalized_logDifferential_circleIntegral_of_factorization
    (rho : ℂ) (m : ℕ) (g h : ℂ → ℂ) {R : ℝ} (hR : 0 < R)
    (hm : 0 < m)
    (hfactor : entireRiemannXi = fun z => (z - rho) ^ m * g z)
    (hg : DifferentiableOn ℂ g (Metric.closedBall rho R))
    (hh : DifferentiableOn ℂ h (Metric.closedBall rho R))
    (hg_deriv : ∀ z, HasDerivAt g (h z) z)
    (hg0 : ∀ z, g z ≠ 0)
    (hpole : CircleIntegrable
      (ZetaLogarithmicPoleCirclePeriod.logarithmicPole rho (m : ℤ)) rho R)
    (hcorr : CircleIntegrable (fun z => h z / g z) rho R) :
    (2 * Real.pi * Complex.I : ℂ)⁻¹ *
        (∮ z in C(rho, R), entireRiemannXiLogDifferential z) =
      - (m : ℂ) := by
  simpa only [entireRiemannXiLogDifferential_eq] using
    entireRiemannXi_normalized_logDerivative_circleIntegral_of_factorization
      rho m g h hR hm hfactor hg hh hg_deriv hg0 hpole hcorr

theorem entireRiemannXi_normalized_logDifferential_circleIntegral_of_factorization_derived
    (rho : ℂ) (m : ℕ) (g h : ℂ → ℂ) {R : ℝ} (hR : 0 < R)
    (hm : 0 < m)
    (hfactor : entireRiemannXi = fun z => (z - rho) ^ m * g z)
    (hg : DifferentiableOn ℂ g (Metric.closedBall rho R))
    (hh : DifferentiableOn ℂ h (Metric.closedBall rho R))
    (hg_deriv : ∀ z, HasDerivAt g (h z) z)
    (hg0 : ∀ z, g z ≠ 0) :
    (2 * Real.pi * Complex.I : ℂ)⁻¹ *
        (∮ z in C(rho, R), entireRiemannXiLogDifferential z) =
      - (m : ℂ) := by
  simpa only [entireRiemannXiLogDifferential_eq] using
    entireRiemannXi_normalized_logDerivative_circleIntegral_of_factorization_derived
      rho m g h hR hm hfactor hg hh hg_deriv hg0

theorem entireRiemannXi_logDerivative_circleIntegral_eq_zero_of_nonvanishing
    (rho : ℂ) {R : ℝ} (hR : 0 < R)
    (hzero : ∀ z ∈ Metric.closedBall rho R, entireRiemannXi z ≠ 0) :
    (∮ z in C(rho, R),
      -(deriv entireRiemannXi z / entireRiemannXi z)) = 0 := by
  have hquot := circleIntegral_div_eq_zero_of_differentiableOn_nonzero
    rho entireRiemannXi (deriv entireRiemannXi) hR.le
      differentiable_entireRiemannXi.differentiableOn
      differentiable_deriv_entireRiemannXi.differentiableOn hzero
  calc
    (∮ z in C(rho, R),
        -(deriv entireRiemannXi z / entireRiemannXi z)) =
      (-1 : ℂ) •
        (∮ z in C(rho, R),
          deriv entireRiemannXi z / entireRiemannXi z) := by
      rw [← circleIntegral.integral_smul]
      congr 1
      funext z
      simp
    _ = 0 := by rw [hquot]; simp

theorem entireRiemannXi_logDerivative_circleIntegral_eq_zero_of_one_lt_re
    (rho : ℂ) {R : ℝ} (hR : 0 < R)
    (hRe : ∀ z ∈ Metric.closedBall rho R, 1 < z.re) :
    (∮ z in C(rho, R),
      -(deriv entireRiemannXi z / entireRiemannXi z)) = 0 := by
  apply entireRiemannXi_logDerivative_circleIntegral_eq_zero_of_nonvanishing
    rho hR
  intro z hz hzero
  have hz0 : z ≠ 0 := by
    intro hz0
    subst z
    have hcontr := hRe (0 : ℂ) hz
    norm_num at hcontr
  have hz1 : z ≠ 1 := by
    intro hz1
    subst z
    have hcontr := hRe (1 : ℂ) hz
    norm_num at hcontr
  rw [entireRiemannXi_eq_riemannXi hz0 hz1] at hzero
  exact (riemannXi_ne_zero_on_closedBall_of_one_lt_re rho R hRe z hz) hzero

theorem entireRiemannXi_logDerivative_circleIntegral_eq_zero_of_re_lt_zero
    (rho : ℂ) {R : ℝ} (hR : 0 < R)
    (hRe : ∀ z ∈ Metric.closedBall rho R, z.re < 0) :
    (∮ z in C(rho, R),
      -(deriv entireRiemannXi z / entireRiemannXi z)) = 0 := by
  apply entireRiemannXi_logDerivative_circleIntegral_eq_zero_of_nonvanishing
    rho hR
  intro z hz hzero
  exact entireRiemannXi_ne_zero_of_re_lt_zero (hRe z hz) hzero

end InfoGeometry.Canonical.ActualEntireRiemannXiLogDerivativeCirclePeriodBridge
