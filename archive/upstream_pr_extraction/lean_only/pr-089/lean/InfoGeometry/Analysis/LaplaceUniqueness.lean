import Mathlib.Tactic
import InfoGeometry.Analysis.LaplaceTransform
import InfoGeometry.Analysis.LaplaceFourierComparison

/-!
# InfoGeometry.Analysis.LaplaceUniqueness

Injectivity and exponential-order infrastructure for the Laplace transform.

This file keeps the genuinely analytic uniqueness layer separate from the raw
transform core, following the same split that mathlib uses for Fourier and
Mellin.

The file currently exposes:

* an AFP-style exponential-order predicate and its basic closure lemmas;
* the Fourier-axis injectivity theorem already proved via Fourier inversion;
* the Laplace/Mellin comparison theorem already proved in
  `LaplaceFourierComparison`.

The classical positive-half-line Lerch uniqueness theorem still belongs here as
future work; this file is the right home for it.
-/

noncomputable section

namespace InfoGeometry.Analysis.LaplaceUniqueness

open scoped BigOperators
open Set MeasureTheory

/-!
## Exponential order

This is the AFP-style growth predicate that underlies Laplace uniqueness.
-/

/-- A function is of exponential order `a` with constant `M`. -/
def exponentialOrder {E : Type*} [NormedAddCommGroup E] (M a : ℝ) (f : ℝ → E) : Prop :=
  0 < M ∧ ∀ᶠ t in Filter.atTop, ‖f t‖ ≤ M * Real.exp (a * t)

namespace exponentialOrder

variable {E : Type*} [NormedAddCommGroup E]

/-- Constructor for exponential order. -/
theorem intro {M a : ℝ} {f : ℝ → E}
    (hM : 0 < M)
    (hf : ∀ᶠ t in Filter.atTop, ‖f t‖ ≤ M * Real.exp (a * t)) :
    exponentialOrder M a f := by
  exact ⟨hM, hf⟩

/-- Extract the positive constant. -/
theorem pos {M a : ℝ} {f : ℝ → E} (hf : exponentialOrder M a f) : 0 < M := hf.1

/-- Extract the eventual growth estimate. -/
theorem eventually {M a : ℝ} {f : ℝ → E} (hf : exponentialOrder M a f) :
    ∀ᶠ t in Filter.atTop, ‖f t‖ ≤ M * Real.exp (a * t) := hf.2

/-- Exponential order is preserved under eventual equality. -/
theorem eventuallyEq {M a : ℝ} {f g : ℝ → E}
    (hg : exponentialOrder M a g)
    (h : ∀ᶠ t in Filter.atTop, f t = g t) :
    exponentialOrder M a f := by
  refine ⟨hg.pos, ?_⟩
  filter_upwards [hg.eventually, h] with t hgt heq
  simpa [heq] using hgt

/-- Exponential order is preserved by tailwise equality. -/
theorem tailEq {M a : ℝ} {f g : ℝ → E}
    (hg : exponentialOrder M a g)
    (k : ℝ) (h : ∀ t, k ≤ t → f t = g t) :
    exponentialOrder M a f := by
  refine eventuallyEq (hg := hg) ?_
  filter_upwards [Filter.eventually_ge_atTop k] with t ht
  exact h t ht

/-- Exponential order is monotone in the growth rate and prefactor. -/
theorem mono {M N a b : ℝ} {f : ℝ → E}
  (hf : exponentialOrder M a f)
  (ha : a ≤ b) (hMN : M ≤ N) :
    exponentialOrder N b f := by
  refine ⟨lt_of_lt_of_le hf.pos hMN, ?_⟩
  filter_upwards [hf.eventually, Filter.eventually_gt_atTop (0 : ℝ)] with t hbound ht
  have hmul : a * t ≤ b * t := by
    exact mul_le_mul_of_nonneg_right ha (le_of_lt ht)
  have hexp : Real.exp (a * t) ≤ Real.exp (b * t) := (Real.exp_le_exp).2 hmul
  have h1 : M * Real.exp (a * t) ≤ N * Real.exp (a * t) := by
    exact mul_le_mul_of_nonneg_right hMN (Real.exp_nonneg _)
  have h2 : N * Real.exp (a * t) ≤ N * Real.exp (b * t) := by
    exact mul_le_mul_of_nonneg_left hexp (le_of_lt (lt_of_lt_of_le hf.pos hMN))
  have hMexp : M * Real.exp (a * t) ≤ N * Real.exp (b * t) := le_trans h1 h2
  exact le_trans hbound hMexp

/-- Exponential order is preserved by negation. -/
theorem uminus_iff {M a : ℝ} {f : ℝ → E} :
    exponentialOrder M a (fun t => - f t) ↔ exponentialOrder M a f := by
  constructor <;> intro hf
  · refine ⟨hf.pos, ?_⟩
    filter_upwards [hf.eventually] with t h
    simpa using h
  · refine ⟨hf.pos, ?_⟩
    filter_upwards [hf.eventually] with t h
    simpa using h

/-- Exponential order is preserved under addition. -/
theorem add {M a : ℝ} {f g : ℝ → E}
    (hf : exponentialOrder M a f) (hg : exponentialOrder M a g) :
    exponentialOrder (2 * M) a (fun t => f t + g t) := by
  refine ⟨by nlinarith [hf.pos], ?_⟩
  filter_upwards [hf.eventually, hg.eventually] with t hf' hg'
  calc
    ‖f t + g t‖ ≤ ‖f t‖ + ‖g t‖ := norm_add_le _ _
    _ ≤ M * Real.exp (a * t) + M * Real.exp (a * t) := by
          exact add_le_add hf' hg'
    _ = (2 * M) * Real.exp (a * t) := by ring

end exponentialOrder

/-!
## Injectivity via Fourier inversion

This is the same method shape used by the Fourier API: reduce Laplace-axis
equality to a Fourier-axis statement and invoke inversion.
-/

section FourierAxis

open scoped FourierTransform RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

/-- Laplace transforms agreeing on the Fourier axis determine the underlying function. -/
theorem unique_on_fourier_axis
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
  exact InfoGeometry.Analysis.LaplaceFourierComparison.laplace_unique_on_fourier_axis
    (f := f) (g := g) hf h'f hg h'g hcf hcg h

/-- Fourier-axis inversion theorem for the native Laplace package. -/
theorem laplace_inverse_on_fourier_axis
    {f : ℝ → E}
    (hf : MeasureTheory.Integrable f) (h'f : MeasureTheory.Integrable (𝓕 f))
    (hcf : Continuous f) :
    𝓕⁻ (fun w : ℝ =>
      InfoGeometry.Analysis.LaplaceTransform.laplaceTransform f
        ((2 * Real.pi * Complex.I) * w)) = f := by
  exact InfoGeometry.Analysis.LaplaceFourierComparison.laplace_fourierInv_on_axis
    (f := f) hf h'f hcf

/--
Positive-axis inversion theorem for the native Laplace package.

This is the Mellin-pullback inversion statement, and it is the classical
positive-axis inversion theorem currently available for the Laplace core.
-/
theorem laplace_inverse_on_positive_axis
    {f : ℝ → E} [CompleteSpace E] (σ : ℝ) {x : ℝ}
    (hx : 0 < x)
    (hf : MellinConvergent (fun t : ℝ => f (-Real.log t)) σ)
    (hFf : Complex.VerticalIntegrable (mellin (fun t : ℝ => f (-Real.log t))) σ)
    (hfx : ContinuousAt (fun t : ℝ => f (-Real.log t)) x) :
    mellinInv σ (InfoGeometry.Analysis.LaplaceTransform.laplaceTransform f) x =
      f (-Real.log x) := by
  exact InfoGeometry.Analysis.LaplaceFourierComparison.laplace_inverse_on_positive_axis
    (f := f) (σ := σ) (x := x) hx hf hFf hfx

/-- Native off-axis inverse Laplace transform on the positive axis. -/
def laplaceInversePos {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (σ : ℝ) (F : ℂ → E) (x : ℝ) : E :=
  mellinInv σ F (Real.exp (-x))

/--
Canonical inverse Laplace transform on the positive axis.

This is the native inverse operator surface for the current Laplace package.
-/
def laplaceInverse {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (σ : ℝ) (F : ℂ → E) (x : ℝ) : E :=
  laplaceInversePos (E := E) σ F x

/--
The native off-axis inverse Laplace transform recovers the original function.

This is the usable inverse transform package available in the current Laplace
layer: it is off-axis in the Mellin/vertical-parameter sense and recovers the
function by pulling back along `x ↦ exp (-x)`.
-/
theorem laplaceInversePos_laplaceTransform_eq
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (σ : ℝ) (f : ℝ → E) (x : ℝ)
    (hf : MellinConvergent (fun t : ℝ => f (-Real.log t)) σ)
    (hFf : Complex.VerticalIntegrable (mellin (fun t : ℝ => f (-Real.log t))) σ)
    (hcf : Continuous f) :
    laplaceInversePos (E := E) σ
      (InfoGeometry.Analysis.LaplaceTransform.laplaceTransform f) x = f x := by
  have hpos : 0 < Real.exp (-x) := Real.exp_pos (-x)
  have hcont : ContinuousAt (fun t : ℝ => f (-Real.log t)) (Real.exp (-x)) := by
    have hlog : ContinuousAt (fun t : ℝ => -Real.log t) (Real.exp (-x)) := by
      simpa using
        (Real.continuousAt_log (ne_of_gt hpos)).neg
    exact hcf.continuousAt.comp hlog
  have hinv :
      mellinInv σ (InfoGeometry.Analysis.LaplaceTransform.laplaceTransform f)
        (Real.exp (-x)) = f x := by
    have hstep :=
      InfoGeometry.Analysis.LaplaceFourierComparison.laplace_inverse_on_positive_axis
        (f := f) (σ := σ) (x := Real.exp (-x)) hpos hf hFf hcont
    calc
      mellinInv σ (InfoGeometry.Analysis.LaplaceTransform.laplaceTransform f)
          (Real.exp (-x))
          = f (-Real.log (Real.exp (-x))) := hstep
      _ = f x := by simp
  simpa [laplaceInversePos] using hinv

/-- The canonical inverse Laplace transform recovers the original function. -/
theorem laplaceInverse_laplaceTransform_eq
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (σ : ℝ) (f : ℝ → E) (x : ℝ)
    (hf : MellinConvergent (fun t : ℝ => f (-Real.log t)) σ)
    (hFf : Complex.VerticalIntegrable (mellin (fun t : ℝ => f (-Real.log t))) σ)
    (hcf : Continuous f) :
    laplaceInverse (E := E) σ
      (InfoGeometry.Analysis.LaplaceTransform.laplaceTransform f) x = f x := by
  simpa [laplaceInverse] using
    (laplaceInversePos_laplaceTransform_eq (E := E) σ f x hf hFf hcf)

/--
Native Laplace injectivity from the canonical inverse operator.

This is the direct Laplace-side uniqueness theorem: once the canonical inverse
recovers a function from its Laplace transform, equal transforms imply equal
functions without routing through the Fourier-axis comparison theorem.
-/
theorem laplace_unique_of_equal_transform
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (σ : ℝ) (f g : ℝ → E)
    (hf : MellinConvergent (fun t : ℝ => f (-Real.log t)) σ)
    (hFg : Complex.VerticalIntegrable (mellin (fun t : ℝ => f (-Real.log t))) σ)
    (hg : MellinConvergent (fun t : ℝ => g (-Real.log t)) σ)
    (hGg : Complex.VerticalIntegrable (mellin (fun t : ℝ => g (-Real.log t))) σ)
    (hcf : Continuous f) (hcg : Continuous g)
    (h : InfoGeometry.Analysis.LaplaceTransform.laplaceTransform f =
      InfoGeometry.Analysis.LaplaceTransform.laplaceTransform g) :
    f = g := by
  ext x
  calc
    f x = laplaceInverse (E := E) σ
        (InfoGeometry.Analysis.LaplaceTransform.laplaceTransform f) x := by
          symm
          exact laplaceInverse_laplaceTransform_eq (E := E) σ f x hf hFg hcf
    _ = laplaceInverse (E := E) σ
        (InfoGeometry.Analysis.LaplaceTransform.laplaceTransform g) x := by
          rw [h]
    _ = g x := by
          exact laplaceInverse_laplaceTransform_eq (E := E) σ g x hg hGg hcg

/-- The vertical-line Laplace transform, packaged under Bromwich terminology. -/
def bromwichVerticalLineTransform {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (σ : ℝ) (f : ℝ → E) : ℝ → E :=
  InfoGeometry.Analysis.LaplaceFourierComparison.verticalLineTransform (E := E) σ f

/-- Bromwich inversion on a vertical line, exported as the direct contour package. -/
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
        FourierTransformInv.fourierInv (bromwichVerticalLineTransform (E := E) σ f) t) = f := by
  simpa [bromwichVerticalLineTransform] using
    (InfoGeometry.Analysis.LaplaceFourierComparison.bromwich_inversion_on_vertical_line
      (f := f) (σ := σ) hf h'f hcf)

/-- Contour deformation on the Bromwich vertical line. -/
theorem bromwich_contour_shift
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (f : ℝ → E) (σ τ : ℝ) :
    bromwichVerticalLineTransform (E := E) σ f =
      bromwichVerticalLineTransform (E := E) τ
        (fun t : ℝ => Complex.exp (-((σ - τ : ℂ) * (t : ℂ))) • f t) := by
  simpa [bromwichVerticalLineTransform] using
    (InfoGeometry.Analysis.LaplaceFourierComparison.verticalLineTransform_shift
      (E := E) (f := f) (σ := σ) (τ := τ))

/--
Direct Bromwich uniqueness on a vertical line.

If two Laplace data agree on the same Bromwich contour and both sorry the
vertical-line inversion hypotheses, then the underlying functions agree.
-/
theorem bromwich_unique_on_vertical_line
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (f g : ℝ → E) (σ : ℝ)
    (hf : MeasureTheory.Integrable (fun t : ℝ =>
      Complex.exp (-(σ * (t : ℂ))) • f t))
    (h'f : MeasureTheory.Integrable
      (FourierTransform.fourier (fun t : ℝ =>
        Complex.exp (-(σ * (t : ℂ))) • f t)))
    (hcf : Continuous f)
    (hg : MeasureTheory.Integrable (fun t : ℝ =>
      Complex.exp (-(σ * (t : ℂ))) • g t))
    (h'g : MeasureTheory.Integrable
      (FourierTransform.fourier (fun t : ℝ =>
        Complex.exp (-(σ * (t : ℂ))) • g t)))
    (hcg : Continuous g)
    (h :
      bromwichVerticalLineTransform (E := E) σ f =
        bromwichVerticalLineTransform (E := E) σ g) :
    f = g := by
  ext t
  calc
    f t =
        Complex.exp ((σ * (t : ℂ))) •
          FourierTransformInv.fourierInv
            (bromwichVerticalLineTransform (E := E) σ f) t := by
      symm
      exact congrArg (fun h => h t)
        (bromwich_inversion_on_vertical_line (f := f) (σ := σ) hf h'f hcf)
    _ =
        Complex.exp ((σ * (t : ℂ))) •
          FourierTransformInv.fourierInv
            (bromwichVerticalLineTransform (E := E) σ g) t := by rw [h]
    _ = g t := by
      exact congrArg (fun h => h t)
        (bromwich_inversion_on_vertical_line (f := g) (σ := σ) hg h'g hcg)

/--
Admissibility data for a genuine Bromwich contour argument.

This is the proof surface the independent contour theorem will eventually need:
half-plane convergence, the damped vertical-line integral, its Fourier-side
integrability, and continuity of the underlying function.
-/
def BromwichContourAdmissible {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] (f : ℝ → E) (σ : ℝ) : Prop :=
  InfoGeometry.Analysis.LaplaceFourierComparison.LaplaceConvergentOnHalfPlane
      (E := E) σ f ∧
  MeasureTheory.Integrable (fun t : ℝ =>
    Complex.exp (-(σ * (t : ℂ))) • f t) ∧
  MeasureTheory.Integrable
    (FourierTransform.fourier (fun t : ℝ =>
      Complex.exp (-(σ * (t : ℂ))) • f t)) ∧
  Continuous f

/--
The direct Bromwich contour package.

This packages the vertical-line contour transform, the contour-shift law, and
the inversion statement under a single proof-carrying interface.
-/
def BromwichContourPackage {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] (f : ℝ → E) (σ : ℝ) : Prop :=
  BromwichContourAdmissible f σ ∧
  (∀ τ : ℝ,
    bromwichVerticalLineTransform (E := E) σ f =
      bromwichVerticalLineTransform (E := E) τ
        (fun t : ℝ => Complex.exp (-((σ - τ : ℂ) * (t : ℂ))) • f t)) ∧
  ((fun t : ℝ =>
    Complex.exp ((σ * (t : ℂ))) •
      FourierTransformInv.fourierInv
        (bromwichVerticalLineTransform (E := E) σ f) t) = f)

/--
Package constructor from the currently available theorem-safe Bromwich
vertical-line inversion and contour-shift lemmas.
-/
theorem bromwichContourPackage_of_hypotheses
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (f : ℝ → E) (σ : ℝ)
    (hA : BromwichContourAdmissible f σ) :
    BromwichContourPackage f σ := by
  refine ⟨hA, ?_, ?_⟩
  · intro τ
    exact bromwich_contour_shift (E := E) (f := f) (σ := σ) (τ := τ)
  · exact bromwich_inversion_on_vertical_line (f := f) (σ := σ) hA.2.1
      hA.2.2.1 hA.2.2.2

end FourierAxis

end InfoGeometry.Analysis.LaplaceUniqueness
