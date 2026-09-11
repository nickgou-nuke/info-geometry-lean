import InfoGeometry.Arithmetic.RiemannZetaEquivalences
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.LogDerivativeLocalFactorizationBridge
import InfoGeometry.Canonical.ActualRiemannXiLogDerivativeBridge

/-!
# Local logarithmic period for the actual completed Riemann `xi`

This owner specializes the existing local-factorization contour theorem to
Mathlib's concrete `riemannXi`.  The local factorization, multiplicity, and
nonvanishing hypotheses remain explicit: this file does not construct the
zero divisor of `riemannXi` and makes no global assertion about its zeros.
-/

noncomputable section

namespace InfoGeometry.Canonical.ActualRiemannXiLogDerivativeCirclePeriodBridge

open Complex
open InfoGeometry.Arithmetic.RiemannZetaEquivalences
open InfoGeometry.Canonical.LogDerivativeLocalFactorizationBridge
open InfoGeometry.Canonical.ActualRiemannXiLogDerivativeBridge

theorem riemannXi_normalized_logDerivative_circleIntegral_of_factorization
    (rho : ℂ) (m : ℕ) (g h : ℂ → ℂ) {R : ℝ} (hR : 0 < R)
    (hm : 0 < m)
    (hfactor : riemannXi = fun z => (z - rho) ^ m * g z)
    (hg : DifferentiableOn ℂ g (Metric.closedBall rho R))
    (hh : DifferentiableOn ℂ h (Metric.closedBall rho R))
    (hg_deriv : ∀ z, HasDerivAt g (h z) z)
    (hg0 : ∀ z, g z ≠ 0)
    (hpole : CircleIntegrable
      (ZetaLogarithmicPoleCirclePeriod.logarithmicPole rho (m : ℤ)) rho R)
    (hcorr : CircleIntegrable (fun z => h z / g z) rho R) :
    (2 * Real.pi * Complex.I : ℂ)⁻¹ *
        (∮ z in C(rho, R), -(deriv riemannXi z / riemannXi z)) =
      - (m : ℂ) := by
  exact normalized_logDerivative_circleIntegral_eq_neg_natCast
    rho m riemannXi g h hR hm hfactor hg hh hg_deriv hg0 hpole hcorr

/-! The same period in the canonical logarithmic-differential readout. -/

theorem riemannXi_normalized_logDifferential_circleIntegral_of_factorization
    (rho : ℂ) (m : ℕ) (g h : ℂ → ℂ) {R : ℝ} (hR : 0 < R)
    (hm : 0 < m)
    (hfactor : riemannXi = fun z => (z - rho) ^ m * g z)
    (hg : DifferentiableOn ℂ g (Metric.closedBall rho R))
    (hh : DifferentiableOn ℂ h (Metric.closedBall rho R))
    (hg_deriv : ∀ z, HasDerivAt g (h z) z)
    (hg0 : ∀ z, g z ≠ 0)
    (hpole : CircleIntegrable
      (ZetaLogarithmicPoleCirclePeriod.logarithmicPole rho (m : ℤ)) rho R)
    (hcorr : CircleIntegrable (fun z => h z / g z) rho R) :
    (2 * Real.pi * Complex.I : ℂ)⁻¹ *
        (∮ z in C(rho, R), actualRiemannXiLogDifferential z) =
      - (m : ℂ) := by
  simpa only [actualRiemannXiLogDifferential_eq] using
    riemannXi_normalized_logDerivative_circleIntegral_of_factorization
      rho m g h hR hm hfactor hg hh hg_deriv hg0 hpole hcorr

/-! Canonical specialization: the contour-integrability premises are derived
from the local analytic hypotheses rather than exposed to downstream users. -/

theorem riemannXi_normalized_logDerivative_circleIntegral_of_factorization_derived
    (rho : ℂ) (m : ℕ) (g h : ℂ → ℂ) {R : ℝ} (hR : 0 < R)
    (hm : 0 < m)
    (hfactor : riemannXi = fun z => (z - rho) ^ m * g z)
    (hg : DifferentiableOn ℂ g (Metric.closedBall rho R))
    (hh : DifferentiableOn ℂ h (Metric.closedBall rho R))
    (hg_deriv : ∀ z, HasDerivAt g (h z) z)
    (hg0 : ∀ z, g z ≠ 0) :
    (2 * Real.pi * Complex.I : ℂ)⁻¹ *
        (∮ z in C(rho, R), -(deriv riemannXi z / riemannXi z)) =
      - (m : ℂ) := by
  exact normalized_logDerivative_circleIntegral_eq_neg_natCast_derived
    rho m riemannXi g h hR hm hfactor hg hh hg_deriv hg0

theorem riemannXi_normalized_logDifferential_circleIntegral_of_factorization_derived
    (rho : ℂ) (m : ℕ) (g h : ℂ → ℂ) {R : ℝ} (hR : 0 < R)
    (hm : 0 < m)
    (hfactor : riemannXi = fun z => (z - rho) ^ m * g z)
    (hg : DifferentiableOn ℂ g (Metric.closedBall rho R))
    (hh : DifferentiableOn ℂ h (Metric.closedBall rho R))
    (hg_deriv : ∀ z, HasDerivAt g (h z) z)
    (hg0 : ∀ z, g z ≠ 0) :
    (2 * Real.pi * Complex.I : ℂ)⁻¹ *
        (∮ z in C(rho, R), actualRiemannXiLogDifferential z) =
      - (m : ℂ) := by
  simpa only [actualRiemannXiLogDifferential_eq] using
    riemannXi_normalized_logDerivative_circleIntegral_of_factorization_derived
      rho m g h hR hm hfactor hg hh hg_deriv hg0

end InfoGeometry.Canonical.ActualRiemannXiLogDerivativeCirclePeriodBridge
