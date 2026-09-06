import InfoGeometry.Arithmetic.BostConnesNativeZetaPartition
import InfoGeometry.Dynamics.SouriauBostConnesFlow

/-!
# Actual zeta logarithmic-gradient sign for the Souriau flow

On the native convergent half-plane `1 < β`, the repository already proves
nonnegativity of the actual `-ζ'/ζ` readout.  This file transports that fact to
the existing scalar Souriau flow.  It proves only a nonnegative flow sign for
`κ ≥ 0`; it does not assert strictness, a critical-line attractor, or a global
zeta dynamical system.
-/

noncomputable section

namespace InfoGeometry.Dynamics.ActualZetaSouriauFlowBridge

open scoped LSeries.notation

open InfoGeometry.Arithmetic.ActualRiemannZetaVonMangoldtBridge
open InfoGeometry.Arithmetic.BostConnesNativeZetaPartition
open InfoGeometry.Dynamics.SouriauBostConnesFlow
open ArithmeticFunction

noncomputable def actualZetaEntropyGradient (β : ℝ) : ℝ :=
  -(actualRiemannZetaLogDerivative (β : ℂ)).re

theorem actualZetaEntropyGradient_eq_neg_vonMangoldt
    {β : ℝ} (hβ : 1 < β) :
    actualZetaEntropyGradient β =
      -(L ↗Λ (β : ℂ)).re := by
  unfold actualZetaEntropyGradient
  rw [actualRiemannZetaLogDerivative_eq_vonMangoldt_LSeries
    (by simpa using hβ)]

theorem actualZetaEntropyGradient_nonpositive
    {β : ℝ} (hβ : 1 < β) :
    actualZetaEntropyGradient β ≤ 0 := by
  change -(actualRiemannZetaLogDerivative (β : ℂ)).re ≤ 0
  have hnonneg : 0 ≤ (actualRiemannZetaLogDerivative (β : ℂ)).re := by
    rw [actualRiemannZetaLogDerivative_eq_vonMangoldt_LSeries
      (by simpa using hβ)]
    have h := partitionSeries_logDerivative_real_nonpos hβ
    rw [partitionSeries_logDerivative_eq_vonMangoldt_LSeries
      (by simpa using hβ)] at h
    exact h
  linarith

noncomputable def actualZetaMetriplecticFlowField
    (κ β : ℝ) : ℝ :=
  metriplecticFlowField κ actualZetaEntropyGradient β

theorem actualZetaMetriplecticFlowField_eq_vonMangoldt
    {κ β : ℝ} (hβ : 1 < β) :
    actualZetaMetriplecticFlowField κ β =
      κ * (L ↗Λ (β : ℂ)).re := by
  unfold actualZetaMetriplecticFlowField metriplecticFlowField
    souriauEntropyGradient
  rw [actualZetaEntropyGradient_eq_neg_vonMangoldt hβ]
  ring

theorem actualZetaMetriplecticFlowField_nonnegative
    {κ β : ℝ} (hκ : 0 ≤ κ) (hβ : 1 < β) :
    0 ≤ actualZetaMetriplecticFlowField κ β := by
  dsimp [actualZetaMetriplecticFlowField, metriplecticFlowField]
  have hg := actualZetaEntropyGradient_nonpositive hβ
  change 0 ≤ -κ * actualZetaEntropyGradient β
  nlinarith [mul_nonneg hκ (neg_nonneg.mpr hg)]

end InfoGeometry.Dynamics.ActualZetaSouriauFlowBridge
