import InfoGeometry.Canonical.ZetaLogDerivativeDeRhamPeriodBridge
import InfoGeometry.Canonical.ZetaLogarithmicPoleCirclePeriod
import InfoGeometry.Arithmetic.RiemannZetaEquivalences

/-!
# Concrete circle-period readout for the logarithmic-derivative datum

This file connects the existing integer bookkeeping owner for isolated zeros
to the genuine local contour-integral kernel.  The factorization hypotheses
are explicit: no factorization of the actual completed zeta function, and no
global de Rham cohomology class, is introduced here.
-/

noncomputable section

namespace InfoGeometry.Canonical.ZetaLogDerivativeCirclePeriodBridge

open Complex
open InfoGeometry.Arithmetic.RiemannZetaEquivalences
open InfoGeometry.Canonical.ZetaLogDerivativeDeRhamPeriod
open InfoGeometry.Canonical.ZetaLogarithmicPoleCirclePeriod

theorem normalized_polePlusHolomorphicCorrection_period_eq_windingPeriod_single
    (z : IsolatedZeroData) (f g h : ℂ → ℂ) {R : ℝ} (hR : 0 < R)
    (hg : DifferentiableOn ℂ g (Metric.closedBall z.center R))
    (hh : DifferentiableOn ℂ h (Metric.closedBall z.center R))
    (hg0 : ∀ w ∈ Metric.closedBall z.center R, g w ≠ 0)
    (hfactor : Set.EqOn f
      (fun w => logarithmicPole z.center z.multiplicity w + h w / g w)
      (Metric.sphere z.center R))
    (hpole : CircleIntegrable
      (logarithmicPole z.center z.multiplicity) z.center R)
    (hcorr : CircleIntegrable (fun w => h w / g w) z.center R) :
    (2 * Real.pi * Complex.I : ℂ)⁻¹ *
        (∮ w in C(z.center, R), f w) =
      (windingPeriod [z] : ℂ) := by
  rw [polePlusHolomorphicCorrection_circleIntegral z.center z.multiplicity f g h
    hR hg hh hg0 hfactor hpole hcorr]
  rw [single_zero_period z]
  field_simp
  norm_num

theorem normalized_riemannXi_log_derivative_period_eq_windingPeriod_single
    (z : IsolatedZeroData) (g h : ℂ → ℂ) {R : ℝ} (hR : 0 < R)
    (hg : DifferentiableOn ℂ g (Metric.closedBall z.center R))
    (hh : DifferentiableOn ℂ h (Metric.closedBall z.center R))
    (hg0 : ∀ w ∈ Metric.closedBall z.center R, g w ≠ 0)
    (hfactor : Set.EqOn riemannXi
      (fun w => logarithmicPole z.center z.multiplicity w + h w / g w)
      (Metric.sphere z.center R))
    (hpole : CircleIntegrable
      (logarithmicPole z.center z.multiplicity) z.center R)
    (hcorr : CircleIntegrable (fun w => h w / g w) z.center R) :
    (2 * Real.pi * Complex.I : ℂ)⁻¹ *
        (∮ w in C(z.center, R), riemannXi w) =
      (windingPeriod [z] : ℂ) := by
  exact normalized_polePlusHolomorphicCorrection_period_eq_windingPeriod_single
    z riemannXi g h hR hg hh hg0 hfactor hpole hcorr

end InfoGeometry.Canonical.ZetaLogDerivativeCirclePeriodBridge
