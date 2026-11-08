import InfoGeometry.Dynamics.ActualZetaCurvatureMetriplecticBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Dynamics.ActualZetaRealFisherMetriplecticBridge

/-!
# Derivative coherence of the actual zeta Fisher and curvature flows

On the real half-plane `1 < beta`, the von-Mangoldt curvature coefficient is
the negative derivative of the Fisher coefficient of the native real partition
readout.  This file packages that derivative identity and transports it to
the existing scalar curvature flow.

No complex-plane Fisher positivity, critical-line dynamics, or asymptotic is
introduced here.
-/

noncomputable section

namespace InfoGeometry.Dynamics.ActualZetaFisherCurvatureCoherenceBridge

open InfoGeometry.Arithmetic.ActualZetaRealPartitionDerivativeBridge
open InfoGeometry.Arithmetic.BostConnesNativeZetaPartition
open InfoGeometry.Dynamics.ActualZetaCurvatureMetriplecticBridge
open InfoGeometry.Dynamics.ActualZetaRealFisherMetriplecticBridge

theorem actualZetaRealFisherInformation_deriv_eq_neg_actualVonMangoldtCurvature
    {beta : ℝ} (hbeta : 1 < beta) :
    deriv actualZetaRealFisherInformation beta =
      -actualVonMangoldtCurvature beta := by
  exact actualZetaRealFisherInformation_deriv_eq_neg_curvature hbeta

theorem actualZetaCurvatureMetriplecticFlow_dissipativeFlow_eq_neg_fisher_deriv
    (beta x : ℝ) (hbeta : 1 < beta) :
    (actualZetaCurvatureMetriplecticFlow beta x hbeta).dissipativeFlow =
      -(deriv actualZetaRealFisherInformation beta) * x := by
  rw [actualZetaCurvatureMetriplecticFlow_dissipativeFlow,
    actualZetaRealFisherInformation_deriv_eq_neg_actualVonMangoldtCurvature
      hbeta]
  ring

theorem actualZetaCurvatureMetriplecticFlow_entropyProduction_eq_neg_fisher_deriv
    (beta x : ℝ) (hbeta : 1 < beta) :
    (actualZetaCurvatureMetriplecticFlow beta x hbeta).entropyProduction =
      -(deriv actualZetaRealFisherInformation beta) * x ^ 2 := by
  rw [actualZetaCurvatureMetriplecticFlow_entropyProduction,
    actualZetaRealFisherInformation_deriv_eq_neg_actualVonMangoldtCurvature
      hbeta]
  ring

theorem actualZetaCurvatureMetriplecticFlow_entropyProduction_zero_iff
    (beta x : ℝ) (hbeta : 1 < beta)
    (hcurv : 0 < actualVonMangoldtCurvature beta) :
    (actualZetaCurvatureMetriplecticFlow beta x hbeta).entropyProduction = 0 ↔
      x = 0 := by
  rw [actualZetaCurvatureMetriplecticFlow_entropyProduction]
  constructor
  · intro hzero
    rcases mul_eq_zero.mp hzero with hcurv0 | hxsq
    · exact False.elim ((ne_of_gt hcurv) hcurv0)
    · exact (sq_eq_zero_iff).mp hxsq
  · intro hx
    simp [hx]

end InfoGeometry.Dynamics.ActualZetaFisherCurvatureCoherenceBridge
