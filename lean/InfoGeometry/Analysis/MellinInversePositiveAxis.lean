import Mathlib.Analysis.MellinInversion
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Analysis.MellinWaveletConformalMapping

/-!
# Mellin inversion on the positive axis

This owner packages the native `mellinInv_mellin_eq` theorem into the repo's
logarithmic-scale dictionary.  It does not claim any new inversion principle;
it only records the positive-axis inversion theorem and its transport through
the logarithmic pullback used by the Mellin/wavelet cylinder.
-/

noncomputable section

namespace InfoGeometry.Analysis.MellinInversePositiveAxis

open scoped BigOperators
open InfoGeometry.Analysis.MellinWaveletConformalMapping

/--
Positive-axis Mellin inversion on a function whose Mellin transform is
convergent at the vertical line `σ`.
-/
theorem mellin_inverse_on_positive_axis
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (σ : ℝ) (f : ℝ → E) {x : ℝ}
    (hx : 0 < x)
    (hf : MellinConvergent f σ)
    (hFf : Complex.VerticalIntegrable (mellin f) σ)
    (hfx : ContinuousAt f x) :
    mellinInv σ (mellin f) x = f x :=
  mellinInv_mellin_eq σ f hx hf hFf hfx

/--
Positive-axis Mellin inversion after logarithmic pullback.

This is the theorem-safe bridge from the Mellin cylinder to the additive
log-time coordinate.
-/
theorem mellin_inverse_on_log_pullback
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (σ : ℝ) (f : ℝ → E) {x : ℝ}
    (hx : 0 < x)
    (hf : MellinConvergent (fun t : ℝ => f (-Real.log t)) σ)
    (hFf : Complex.VerticalIntegrable
      (mellin (fun t : ℝ => f (-Real.log t))) σ)
    (hfx : ContinuousAt (fun t : ℝ => f (-Real.log t)) x) :
    mellinInv σ (mellin (fun t : ℝ => f (-Real.log t))) x =
      f (-Real.log x) :=
  mellinInv_mellin_eq σ (fun t : ℝ => f (-Real.log t)) hx hf hFf hfx

/--
The logarithmic pullback theorem in the repo's scale dictionary.

This is the same positive-axis inversion statement packaged in the form used by
`MellinWaveletConformalMapping`.
-/
theorem mellin_inverse_on_log_time
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (σ : ℝ) (f : ℝ → E) {x : ℝ}
    (hx : 0 < x)
    (hf : MellinConvergent (fun t : ℝ => f (-Real.log t)) σ)
    (hFf : Complex.VerticalIntegrable
      (mellin (fun t : ℝ => f (-Real.log t))) σ)
    (hfx : ContinuousAt (fun t : ℝ => f (-Real.log t)) x) :
    mellinInv σ (InfoGeometry.Analysis.LaplaceTransform.laplaceTransform f) x =
      f (-Real.log x) := by
  exact InfoGeometry.Analysis.LaplaceFourierComparison.laplace_inverse_on_positive_axis
    (f := f) (σ := σ) (x := x) hx hf hFf hfx

end InfoGeometry.Analysis.MellinInversePositiveAxis
