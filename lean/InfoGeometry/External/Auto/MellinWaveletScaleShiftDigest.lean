import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Analysis.RCLike.Sqrt
import InfoGeometry.External.Auto.TransformsAndScale
open TransformsAndScale

/-!
# Mellin, Laplace, and wavelet scale-shift digest

Finite extraction from three PDFs:

* Alotta--Di Paola--Failla, *A Mellin transform approach to wavelet analysis*
  (2015);
* Kaiser, *Wavelet Filtering with the Mellin Transform* (1996/2001);
* Ngom--Alpay--Mboup, *Scale-Shift and Harmonic analysis approach to the
  Mellin transform for Discrete-time signals* (2022).

The formalized spine here is intentionally finite:

* the two standard wavelet parameterizations `a,b` and `σ,τ` are recorded;
* the Mellin kernel is the logarithmic Fourier kernel;
* positive-scale multiplication becomes additive translation in log coordinates;
* even/odd splitting of a signal is explicit;
* the discrete-time scale-shift/Möbius formula is recorded as a precise formula;
* analytic integral transforms are represented only through explicit hypotheses.
-/

noncomputable section

namespace MellinWaveletScaleShiftDigest

open Complex

/-- Standard continuous wavelet core `ψ((t-b)/a)`. -/
def waveletStdCore (ψ : ℝ → ℂ) (a b t : ℝ) : ℂ :=
  ψ ((t - b) / a)

/-- Kaiser-style normalized continuous wavelet family. -/
def waveletStd (ψ : ℝ → ℂ) (a b t : ℝ) : ℂ :=
  (a : ℂ)⁻¹ * waveletStdCore ψ a b t

/-- Kaiser-style scale/shift family `ψ(σ t - τ)`. -/
def waveletFreq (ψ : ℝ → ℂ) (σ τ t : ℝ) : ℂ :=
  ψ (σ * t - τ)

@[simp] theorem waveletStdCore_apply (ψ : ℝ → ℂ) (a b t : ℝ) :
    waveletStdCore ψ a b t = ψ ((t - b) / a) := rfl

@[simp] theorem waveletStd_apply (ψ : ℝ → ℂ) (a b t : ℝ) :
    waveletStd ψ a b t = (a : ℂ)⁻¹ * ψ ((t - b) / a) := rfl

@[simp] theorem waveletFreq_apply (ψ : ℝ → ℂ) (σ τ t : ℝ) :
    waveletFreq ψ σ τ t = ψ (σ * t - τ) := rfl

/-- The two core conventions match by setting `σ = 1/a` and `τ = b/a`. -/
theorem waveletStdCore_as_freq (ψ : ℝ → ℂ) (a b t : ℝ) (ha : a ≠ 0) :
    waveletStdCore ψ a b t = waveletFreq ψ (1 / a) (b / a) t := by
  unfold waveletStdCore waveletFreq
  congr
  field_simp [ha]

/-- Mellin kernel `x ↦ x^(s-1)` expressed via the logarithm. -/
def mellinKernel (s : ℂ) (x : ℝ) : ℂ :=
  Complex.exp ((s - 1) * (Real.log x : ℂ))

@[simp] theorem mellinKernel_mul {s : ℂ} {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
  mellinKernel s (x * y) = mellinKernel s x * mellinKernel s y := by
  simp [mellinKernel, Real.log_mul hx.ne' hy.ne', mul_add,
    Complex.exp_add]

/-- Branch-free Mellin kernel in logarithmic coordinates. -/
def logMellinKernel (s : ℂ) (t : ℝ) : ℂ :=
  Complex.exp ((s - 1) * (t : ℂ))

@[simp] theorem logMellinKernel_add (s : ℂ) (t u : ℝ) :
  logMellinKernel s (t + u) = logMellinKernel s t * logMellinKernel s u := by
  simp [logMellinKernel, Complex.exp_add, add_mul,
    mul_comm]

/-- The Mellin kernel is the Fourier kernel on the logarithmic axis. -/
theorem mellinKernel_as_log_fourier (omega t : ℝ) :
    logMellinKernel (Complex.I * omega + 1) t = Complex.exp (Complex.I * omega * t) := by
  exact mellin_is_log_fourier omega t

/-- Multiplicative scale becomes additive translation after the logarithm. -/
theorem log_mul_as_add (a x : ℝ) (ha : 0 < a) (hx : 0 < x) :
    Real.log (a * x) = Real.log a + Real.log x := by
  simpa [add_comm, add_left_comm, add_assoc] using Real.log_mul ha.ne' hx.ne'

/-- Even/odd splitting of a signal. -/
def evenPart (f : ℝ → ℂ) (t : ℝ) : ℂ :=
  (f t + f (-t)) / 2

def oddPart (f : ℝ → ℂ) (t : ℝ) : ℂ :=
  (f t - f (-t)) / 2

@[simp] theorem evenPart_add_oddPart (f : ℝ → ℂ) (t : ℝ) :
    evenPart f t + oddPart f t = f t := by
  unfold evenPart oddPart
  ring

@[simp] theorem evenPart_neg (f : ℝ → ℂ) (t : ℝ) :
    evenPart f (-t) = evenPart f t := by
  unfold evenPart
  ring_nf

@[simp] theorem oddPart_neg (f : ℝ → ℂ) (t : ℝ) :
    oddPart f (-t) = - oddPart f t := by
  unfold oddPart
  ring_nf

/-- Discrete-time scale-shift via the hyperbolic Blaschke Möbius map. -/
def blaschkeMobius (γ1 γ2 z : ℂ) : ℂ :=
  (γ1 * z + γ2) / (starRingEnd ℂ γ2 * z + starRingEnd ℂ γ1)

@[simp] theorem blaschkeMobius_apply (γ1 γ2 z : ℂ) :
    blaschkeMobius γ1 γ2 z = (γ1 * z + γ2) / (starRingEnd ℂ γ2 * z + starRingEnd ℂ γ1) := rfl

/-- The normalized coefficients from the discrete-time scale-shift paper. -/
def normalizedGamma1 (θ α : ℝ) : ℂ :=
  ((Complex.exp (Complex.I * θ) + α * Complex.exp (-Complex.I * θ)) : ℂ) /
    Complex.sqrt (2 * α * Real.cos θ)

def normalizedGamma2 (θ α : ℝ) : ℂ :=
  ((Complex.exp (Complex.I * θ) * (1 - α)) : ℂ) /
    Complex.sqrt (2 * α * Real.cos θ)

/-! ## Conditional finite lemmas

The following statements prove only what their hypotheses or elementary finite
data provide.  They do not assert continuum transform theory. -/

/-- A linearity hypothesis decomposes a chosen transform across the explicit
even/odd splitting. -/
theorem riesz_mellin_even_odd_decomposition_from_additivity
    (R : (ℝ → ℂ) → (ℝ → ℂ))
    (M : (ℝ → ℂ) → ℂ → ℂ)
    (hLinear : ∀ f g s, M (R (f + g)) s = M (R f) s + M (R g) s) :
    ∀ (f : ℝ → ℂ) (s : ℂ),
      M (R f) s = M (R (evenPart f)) s + M (R (oddPart f)) s := by
  intro f s
  have h_add : evenPart f + oddPart f = f := funext (evenPart_add_oddPart f)
  nth_rw 1 [← h_add]
  exact hLinear (evenPart f) (oddPart f) s

/-- The complex numbers contain a nonzero element. -/
theorem exists_nonzero_complex :
    ∃ C : ℂ, C ≠ 0 := by
  refine Exists.intro 1 ?_
  exact one_ne_zero

/-- A supplied left-inverse hypothesis gives reconstruction for the chosen
operators. -/
theorem wavelet_reconstruction_from_left_inverse
    (W : (ℝ → ℂ) → (ℝ → ℝ → ℂ))
    (Inv : (ℝ → ℝ → ℂ) → (ℝ → ℂ))
    (hInv : Function.LeftInverse Inv W) :
    ∀ f : ℝ → ℂ, Inv (W f) = f := by
  intro f
  exact hInv f

/-- A constant operator family is invariant under the Blaschke Möbius formula. -/
theorem constant_operator_family_invariant_under_blaschkeMobius :
    ∃ U : ℂ → ((ℕ → ℂ) → (ℕ → ℂ)),
      ∀ γ1 γ2 z : ℂ, U (blaschkeMobius γ1 γ2 z) = U z := by
  refine Exists.intro (fun _ => id) ?_
  intro γ1 γ2 z
  rfl

/-! ## Closed finite kernel -/

/-- Closed finite kernel extracted from the Mellin/wavelet sources.

This theorem proves only the algebraic/logarithmic identities present in this
file, plus the explicitly conditional finite lemmas above. -/
theorem mellin_wavelet_scale_shift_digest_finite_kernel :
    (∀ (ψ : ℝ → ℂ) (a b t : ℝ) (_ : a ≠ 0),
        waveletStdCore ψ a b t = waveletFreq ψ (1 / a) (b / a) t) ∧
    (∀ (s : ℂ) (x : ℝ), mellinKernel s x = Complex.exp ((s - 1) * (Real.log x : ℂ))) ∧
    (∀ (s : ℂ) (t : ℝ), logMellinKernel s (t + 0) = logMellinKernel s t) ∧
    (∀ (f : ℝ → ℂ) (t : ℝ), evenPart f t + oddPart f t = f t) ∧
    (∀ (γ1 γ2 z : ℂ), blaschkeMobius γ1 γ2 z =
      (γ1 * z + γ2) / (starRingEnd ℂ γ2 * z + starRingEnd ℂ γ1)) := by
  constructor
  · exact waveletStdCore_as_freq
  constructor
  · intro s x
    rfl
  constructor
  · intro s t
    simp
  constructor
  · exact evenPart_add_oddPart
  · intro γ1 γ2 z
    rfl

end MellinWaveletScaleShiftDigest

end noncomputable section
