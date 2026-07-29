import Mathlib.Tactic
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.MellinInversion
import InfoGeometry.Analysis.LaplaceTransform

/-!
# InfoGeometry.Analysis.LaplaceFourierComparison

Comparison lemmas between the native Laplace kernel and the Fourier-axis
specialization.

This file stays theorem-safe:
* it does not claim Laplace inversion;
* it does not claim uniqueness;
* it does not claim any analytic continuation.
It only records the Fourier-axis identification already present in the core
kernel definition.
-/

noncomputable section

namespace InfoGeometry.Analysis.LaplaceFourierComparison

open InfoGeometry.Analysis.LaplaceTransform
open scoped FourierTransform RealInnerProductSpace

section FourierUniqueness

variable {V E : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [MeasurableSpace V] [BorelSpace V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

/-- On the Fourier axis, the Laplace kernel is an explicit oscillatory kernel. -/
theorem laplaceKernel_fourierChar_exp (w t : ℝ) :
    laplaceKernel ((2 * Real.pi * Complex.I) * w) t =
      Complex.exp ((↑(2 * Real.pi * (-(w * t))) : ℂ) * Complex.I) := by
  rw [laplaceKernel]
  simp [mul_comm, mul_left_comm, mul_assoc, mul_neg, neg_mul]

/-- On the Fourier axis, the Laplace kernel is exactly the Fourier character kernel. -/
theorem laplaceKernel_fourierChar (w t : ℝ) :
    laplaceKernel ((2 * Real.pi * Complex.I) * w) t = Real.fourierChar (-(w * t)) := by
  simpa [Real.fourierChar_apply] using
    (laplaceKernel_fourierChar_exp (w := w) (t := t))

/-- On the Fourier axis, the Laplace transform is the Fourier-character integral. -/
theorem laplaceTransform_eq_fourierChar
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (f : ℝ → E) (w : ℝ) :
    InfoGeometry.Analysis.LaplaceTransform.laplaceTransform f ((2 * Real.pi * Complex.I) * w) =
      ∫ t : ℝ, (Real.fourierChar (-(w * t)) : ℂ) • f t := by
  simpa [InfoGeometry.Analysis.LaplaceTransform.laplaceTransform,
    InfoGeometry.Analysis.LaplaceTransform.laplaceIntegral,
    laplaceKernel_fourierChar, Circle.smul_def] using
    (rfl :
      InfoGeometry.Analysis.LaplaceTransform.laplaceTransform f
        ((2 * Real.pi * Complex.I) * w) =
      InfoGeometry.Analysis.LaplaceTransform.laplaceTransform f
        ((2 * Real.pi * Complex.I) * w))

/-- A `HasLaplace` readout on the Fourier axis is a Fourier-character integral readout. -/
theorem HasLaplace.fourier_readout
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {f : ℝ → E} {w : ℝ} {m : E}
    (hf : InfoGeometry.Analysis.LaplaceTransform.HasLaplace f
      ((2 * Real.pi * Complex.I) * w) m) :
    m =
      ∫ t : ℝ, (Real.fourierChar (-(w * t)) : ℂ) • f t := by
  rcases hf with ⟨_hfconv, hfm⟩
  rw [← hfm]
  exact laplaceTransform_eq_fourierChar (f := f) (w := w)

/-- Fourier transform uniqueness from inversion. -/
theorem fourier_unique_of_equal_transform
    {f g : V → E}
    (hf : MeasureTheory.Integrable f) (h'f : MeasureTheory.Integrable (𝓕 f))
    (hg : MeasureTheory.Integrable g) (h'g : MeasureTheory.Integrable (𝓕 g))
    (hcf : Continuous f) (hcg : Continuous g)
    (h : 𝓕 f = 𝓕 g) :
    f = g := by
  ext v
  calc
    f v = 𝓕⁻ (𝓕 f) v := by
      symm
      exact hf.fourierInv_fourier_eq h'f hcf.continuousAt
    _ = 𝓕⁻ (𝓕 g) v := by rw [h]
    _ = g v := by
      exact hg.fourierInv_fourier_eq h'g hcg.continuousAt

/--
Genuine injectivity on the Fourier axis:
if two Laplace transforms agree on the imaginary-frequency line, then the
underlying functions agree, provided the Fourier-side inversion hypotheses hold.

This is the theorem-safe injectivity result currently available for the Laplace
API; it is derived through Fourier inversion rather than by claiming a native
Laplace inversion theorem.
-/
theorem laplace_unique_on_fourier_axis
    {f g : ℝ → E}
    (hf : MeasureTheory.Integrable f) (h'f : MeasureTheory.Integrable (𝓕 f))
    (hg : MeasureTheory.Integrable g) (h'g : MeasureTheory.Integrable (𝓕 g))
    (hcf : Continuous f) (hcg : Continuous g)
    (h : ∀ w : ℝ,
      InfoGeometry.Analysis.LaplaceTransform.laplaceTransform f
        ((2 * Real.pi * Complex.I) * w) =
      InfoGeometry.Analysis.LaplaceTransform.laplaceTransform g
        ((2 * Real.pi * Complex.I) * w)) :
    f = g := by
  have hF : 𝓕 f = 𝓕 g := by
    ext w
    have hfw :
        InfoGeometry.Analysis.LaplaceTransform.laplaceTransform f
          ((2 * Real.pi * Complex.I) * w) = 𝓕 f w := by
      simpa [Real.fourier_eq] using
        (laplaceTransform_eq_fourierChar (f := f) (w := w))
    have hgw :
        InfoGeometry.Analysis.LaplaceTransform.laplaceTransform g
          ((2 * Real.pi * Complex.I) * w) = 𝓕 g w := by
      simpa [Real.fourier_eq] using
        (laplaceTransform_eq_fourierChar (f := g) (w := w))
    calc
      𝓕 f w =
          InfoGeometry.Analysis.LaplaceTransform.laplaceTransform f
            ((2 * Real.pi * Complex.I) * w) := by
            symm
            exact hfw
      _ = InfoGeometry.Analysis.LaplaceTransform.laplaceTransform g
            ((2 * Real.pi * Complex.I) * w) := h w
      _ = 𝓕 g w := hgw
  exact fourier_unique_of_equal_transform (f := f) (g := g) hf h'f hg h'g hcf hcg hF

/--
Continuity on the Fourier axis:
the Fourier-character kernel appearing in the Laplace comparison is continuous
whenever the underlying function is integrable.
-/
theorem laplaceFourierAxis_continuous
    {f : ℝ → E}
    (hf : MeasureTheory.Integrable f) :
    Continuous fun w : ℝ =>
      ∫ t : ℝ, (Real.fourierChar (-(w * t)) : ℂ) • f t := by
  have h :=
    (VectorFourier.fourierIntegral_continuous (e := Real.fourierChar)
      (μ := MeasureTheory.volume)
      (L := (LinearMap.mul ℝ ℝ : ℝ →ₗ[ℝ] ℝ →ₗ[ℝ] ℝ))
      Real.continuous_fourierChar (by
        simpa using (continuous_mul : Continuous fun p : ℝ × ℝ => p.1 * p.2)) hf)
  unfold VectorFourier.fourierIntegral at h
  simpa [mul_comm] using h

/-- The Laplace transform is continuous on the Fourier axis under integrability. -/
theorem laplaceTransform_continuous_on_fourier_axis
    {f : ℝ → E}
    (hf : MeasureTheory.Integrable f) :
    Continuous fun w : ℝ =>
      InfoGeometry.Analysis.LaplaceTransform.laplaceTransform f
        ((2 * Real.pi * Complex.I) * w) := by
  simpa [laplaceTransform_eq_fourierChar] using
    laplaceFourierAxis_continuous (f := f) hf

/--
Fourier-axis inversion for the Laplace transform.

If the Laplace transform is read on the imaginary-frequency line, then the
Fourier inverse recovers the original function under the usual Fourier
inversion hypotheses.
-/
theorem laplace_fourierInv_on_axis
    {f : ℝ → E}
    (hf : MeasureTheory.Integrable f) (h'f : MeasureTheory.Integrable (𝓕 f))
    (hcf : Continuous f) :
    𝓕⁻ (fun w : ℝ =>
      InfoGeometry.Analysis.LaplaceTransform.laplaceTransform f
        ((2 * Real.pi * Complex.I) * w)) = f := by
  have hF :
      (fun w : ℝ =>
        InfoGeometry.Analysis.LaplaceTransform.laplaceTransform f
          ((2 * Real.pi * Complex.I) * w)) = 𝓕 f := by
    ext w
    simpa [Real.fourier_eq] using
      (laplaceTransform_eq_fourierChar (f := f) (w := w))
  calc
    𝓕⁻ (fun w : ℝ =>
      InfoGeometry.Analysis.LaplaceTransform.laplaceTransform f
        ((2 * Real.pi * Complex.I) * w))
        = 𝓕⁻ (𝓕 f) := by rw [hF]
    _ = f := by
      exact hcf.fourierInv_fourier_eq hf h'f

/-- Half-plane convergence predicate for the Laplace transform. -/
def LaplaceConvergentOnHalfPlane {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (σ : ℝ) (f : ℝ → E) : Prop :=
  ∀ {s : ℂ}, σ < s.re → InfoGeometry.Analysis.LaplaceTransform.LaplaceConvergent
    MeasureTheory.volume f s

/-- Vertical-line Laplace transform at real part `σ`. -/
def verticalLineTransform {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (σ : ℝ) (f : ℝ → E) : ℝ → E :=
  fun w => InfoGeometry.Analysis.LaplaceTransform.laplaceTransform f
    ((σ : ℂ) + (2 * Real.pi * Complex.I) * w)

/-- On a vertical line, the Laplace transform is the Fourier transform of a damped function. -/
theorem verticalLineTransform_eq_fourier
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (f : ℝ → E) (σ : ℝ) :
    verticalLineTransform (E := E) σ f =
      FourierTransform.fourier (fun t : ℝ =>
        Complex.exp (-(σ * (t : ℂ))) • f t) := by
  ext w
  have hshift :
      InfoGeometry.Analysis.LaplaceTransform.laplaceTransform f
        ((σ : ℂ) + (2 * Real.pi * Complex.I) * w) =
      InfoGeometry.Analysis.LaplaceTransform.laplaceTransform
        (fun t : ℝ => Complex.exp (-(σ * (t : ℂ))) • f t)
        ((2 * Real.pi * Complex.I) * w) := by
    rw [add_comm]
    simpa [InfoGeometry.Analysis.LaplaceTransform.laplaceTransform,
      InfoGeometry.Analysis.LaplaceTransform.laplaceIntegral,
      InfoGeometry.Analysis.LaplaceTransform.laplaceKernel]
      using
        (InfoGeometry.Analysis.LaplaceTransform.laplaceTransform.add_spectral
          (E := E) (f := f)
          (s := (2 * Real.pi * Complex.I) * w) (c := (σ : ℂ)))
  calc
    verticalLineTransform (E := E) σ f w
        = InfoGeometry.Analysis.LaplaceTransform.laplaceTransform
            (fun t : ℝ => Complex.exp (-(σ * (t : ℂ))) • f t)
            ((2 * Real.pi * Complex.I) * w) := hshift
    _ = FourierTransform.fourier (fun t : ℝ =>
          Complex.exp (-(σ * (t : ℂ))) • f t) w := by
          simpa [Real.fourier_eq]
            using
              (laplaceTransform_eq_fourierChar
                (f := fun t : ℝ => Complex.exp (-(σ * (t : ℂ))) • f t)
                (w := w))

/-- Fourier inversion of the damped vertical-line Laplace transform. -/
theorem verticalLineTransform_fourierInv_eq
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (f : ℝ → E) (σ : ℝ)
    (hf : MeasureTheory.Integrable (fun t : ℝ =>
      Complex.exp (-(σ * (t : ℂ))) • f t))
    (h'f : MeasureTheory.Integrable
      (FourierTransform.fourier (fun t : ℝ =>
        Complex.exp (-(σ * (t : ℂ))) • f t)))
    (hcf : Continuous f) :
    FourierTransformInv.fourierInv (verticalLineTransform (E := E) σ f) =
      fun t : ℝ => Complex.exp (-(σ * (t : ℂ))) • f t := by
  rw [verticalLineTransform_eq_fourier]
  have hcont : Continuous fun t : ℝ => Complex.exp (-(σ * (t : ℂ))) • f t := by
    continuity
  exact hcont.fourierInv_fourier_eq hf h'f

/--
Native off-axis inversion on a vertical line: the inverse Fourier transform of
the vertical-line Laplace data recovers the damped original function.
-/
theorem laplace_inverse_on_vertical_line
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (f : ℝ → E) (σ : ℝ)
    (hf : MeasureTheory.Integrable (fun t : ℝ =>
      Complex.exp (-(σ * (t : ℂ))) • f t))
    (h'f : MeasureTheory.Integrable
      (FourierTransform.fourier (fun t : ℝ =>
        Complex.exp (-(σ * (t : ℂ))) • f t)))
    (hcf : Continuous f) :
    (fun t : ℝ =>
      Complex.exp ((σ * (t : ℂ))) •
        FourierTransformInv.fourierInv (verticalLineTransform (E := E) σ f) t) = f := by
  ext t
  rw [verticalLineTransform_fourierInv_eq (f := f) (σ := σ) hf h'f hcf]
  rw [smul_smul]
  rw [← Complex.exp_add]
  simp

/--
Bromwich-style inversion statement on a vertical line.

This is the same contour-safe inverse package as `laplace_inverse_on_vertical_line`,
recorded under the classical name.
-/
theorem bromwich_inversion_on_vertical_line
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (f : ℝ → E) (σ : ℝ)
    (hf : MeasureTheory.Integrable (fun t : ℝ =>
      Complex.exp (-(σ * (t : ℂ))) • f t))
    (h'f : MeasureTheory.Integrable
      (FourierTransform.fourier (fun t : ℝ =>
        Complex.exp (-(σ * (t : ℂ))) • f t)))
    (hcf : Continuous f) :
    (fun t : ℝ =>
      Complex.exp ((σ * (t : ℂ))) •
        FourierTransformInv.fourierInv (verticalLineTransform (E := E) σ f) t) = f :=
  laplace_inverse_on_vertical_line (f := f) (σ := σ) hf h'f hcf

/--
Vertical-line contour deformation:
changing the real part `σ` is equivalent to twisting the input by the
corresponding exponential weight.
-/
theorem verticalLineTransform_shift
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (f : ℝ → E) (σ τ : ℝ) :
    verticalLineTransform (E := E) σ f =
      verticalLineTransform (E := E) τ
        (fun t : ℝ => Complex.exp (-((σ - τ : ℂ) * (t : ℂ))) • f t) := by
  ext w
  simpa [verticalLineTransform, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
    using
      (InfoGeometry.Analysis.LaplaceTransform.laplaceTransform.add_spectral
        (E := E) (f := f) (s := (τ : ℂ) + (2 * Real.pi * Complex.I) * w)
        (c := (σ - τ : ℂ)))

end FourierUniqueness

section MellinComparison

open Real Complex Set MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

private theorem rexp_neg_deriv_aux :
    ∀ x ∈ univ, HasDerivWithinAt (rexp ∘ Neg.neg) (-rexp (-x)) univ x :=
  fun x _ ↦ mul_neg_one (rexp (-x)) ▸
    ((Real.hasDerivAt_exp (-x)).comp x (hasDerivAt_neg x)).hasDerivWithinAt

private theorem rexp_neg_image_aux : rexp ∘ Neg.neg '' univ = Ioi 0 := by
  rw [Set.image_comp, Set.image_univ_of_surjective neg_surjective, Set.image_univ, Real.range_exp]

private theorem rexp_neg_injOn_aux : univ.InjOn (rexp ∘ Neg.neg) :=
  Real.exp_injective.injOn.comp neg_injective.injOn (univ.mapsTo_univ _)

private theorem rexp_cexp_aux (x : ℝ) (s : ℂ) (f : E) :
    rexp (-x) • cexp (-↑x) ^ (s - 1) • f = cexp (-s * ↑x) • f := by
  change (rexp (-x) : ℂ) • _ = _ • f
  rw [← smul_assoc, smul_eq_mul]
  push_cast
  conv in cexp _ * _ => lhs; rw [← cpow_one (cexp _)]
  rw [← cpow_add _ _ (Complex.exp_ne_zero _), cpow_def_of_ne_zero (Complex.exp_ne_zero _),
    Complex.log_exp (by simp [pi_pos]) (by simpa using pi_nonneg)]
  ring_nf

/--
The Mellin transform of the logarithmic pullback is the whole-line Laplace transform.

This is the native comparison theorem between the Mellin `t ↦ t^(s-1)` kernel on `Ioi 0`
and the Laplace kernel after the substitution `t = exp (-u)`.
It is a comparison theorem, not an inversion theorem.
-/
theorem mellin_logPullback_eq_laplaceTransform
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (f : ℝ → E) (s : ℂ) :
    mellin (fun t : ℝ => f (-Real.log t)) s =
      InfoGeometry.Analysis.LaplaceTransform.laplaceTransform f s := by
  rw [mellin, InfoGeometry.Analysis.LaplaceTransform.laplaceTransform,
    InfoGeometry.Analysis.LaplaceTransform.laplaceIntegral]
  rw [← rexp_neg_image_aux, integral_image_eq_integral_abs_deriv_smul
    MeasurableSet.univ rexp_neg_deriv_aux rexp_neg_injOn_aux]
  simp [Real.log_exp, rexp_cexp_aux, mul_comm, mul_left_comm, mul_assoc,
    InfoGeometry.Analysis.LaplaceTransform.laplaceKernel]

/-- A `HasMellin` readout on the logarithmic pullback is a Laplace readout. -/
theorem HasMellin.laplace_readout
    {f : ℝ → E} {s : ℂ} {m : E}
    (hf : HasMellin (fun t : ℝ => f (-Real.log t)) s m) :
    m = InfoGeometry.Analysis.LaplaceTransform.laplaceTransform f s := by
  rcases hf with ⟨_hconv, hm⟩
  simpa [HasMellin] using hm.symm.trans
    (mellin_logPullback_eq_laplaceTransform (f := f) (s := s))

/--
Genuine injectivity on the Mellin side:
if two functions have the same Mellin transform, then they agree on the positive
real axis, provided the Mellin inversion hypotheses hold.

This is the theorem-safe injectivity result currently available for the Mellin
comparison route.
-/
theorem mellin_unique_on_positive_axis
    {f g : ℝ → E} [CompleteSpace E] (σ : ℝ)
    (hf : MellinConvergent f σ) (hFf : VerticalIntegrable (mellin f) σ)
    (hg : MellinConvergent g σ) (hFg : VerticalIntegrable (mellin g) σ)
    (hcf : Continuous f) (hcg : Continuous g)
    (h : mellin f = mellin g) :
    ∀ x : ℝ, 0 < x → f x = g x := by
  intro x hx
  calc
    f x = mellinInv σ (mellin f) x := by
      symm
      exact mellinInv_mellin_eq (σ := σ) (f := f) (x := x) hx hf hFf hcf.continuousAt
    _ = mellinInv σ (mellin g) x := by rw [h]
    _ = g x := by
      exact mellinInv_mellin_eq (σ := σ) (f := g) (x := x) hx hg hFg hcg.continuousAt

/--
Positive-axis inversion for the Laplace transform via the Mellin pullback.

This is the classical inversion statement available natively in the current
package: after logarithmic pullback, the Mellin inverse recovers the original
function on the positive axis.
-/
theorem laplace_inverse_on_positive_axis
    {f : ℝ → E} [CompleteSpace E] (σ : ℝ) {x : ℝ}
    (hx : 0 < x)
    (hf : MellinConvergent (fun t : ℝ => f (-Real.log t)) σ)
    (hFf : VerticalIntegrable (mellin (fun t : ℝ => f (-Real.log t))) σ)
    (hfx : ContinuousAt (fun t : ℝ => f (-Real.log t)) x) :
    mellinInv σ (InfoGeometry.Analysis.LaplaceTransform.laplaceTransform f) x =
      f (-Real.log x) := by
  have hLap :
      InfoGeometry.Analysis.LaplaceTransform.laplaceTransform f =
        mellin (fun t : ℝ => f (-Real.log t)) := by
    funext s
    symm
    exact mellin_logPullback_eq_laplaceTransform (f := f) (s := s)
  calc
    mellinInv σ (InfoGeometry.Analysis.LaplaceTransform.laplaceTransform f) x
        = mellinInv σ (mellin (fun t : ℝ => f (-Real.log t))) x := by rw [hLap]
    _ = f (-Real.log x) := by
          exact mellinInv_mellin_eq (σ := σ) (f := fun t : ℝ => f (-Real.log t))
            (x := x) hx hf hFf hfx

end MellinComparison

end InfoGeometry.Analysis.LaplaceFourierComparison
