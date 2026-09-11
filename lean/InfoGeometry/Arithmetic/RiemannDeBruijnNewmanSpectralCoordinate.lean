import Mathlib.Analysis.Complex.Trigonometric
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Analysis.Complex.Exponential

open Complex

namespace InfoGeometry.Arithmetic.RiemannDeBruijnNewman

/-!
# Spectral coordinate for a De Bruijn--Newman-style family

This owner contains only the finite complex-coordinate algebra.  It does not
construct the Riemann heat family, prove a zero-localisation theorem, or
identify a threshold with the Riemann hypothesis.
-/

noncomputable def spectralCoordinate (a E : ℝ) : ℂ :=
  (E : ℂ) - (a : ℂ) * I

theorem cosh_complex_eq_cos_spectral (a E u : ℝ) :
    Complex.cosh ((↑a + ↑E * I) * ↑u) =
      Complex.cos (spectralCoordinate a E * ↑u) := by
  dsimp [spectralCoordinate, Complex.cos, Complex.cosh]
  have h1 : I * ((↑E - ↑a * I) * ↑u) = (↑a + ↑E * I) * ↑u := by
    calc
      I * ((↑E - ↑a * I) * ↑u)
          = I * ↑E * ↑u - I * ↑a * I * ↑u := by ring
      _ = ↑E * I * ↑u - ↑a * (I * I) * ↑u := by ring
      _ = ↑E * I * ↑u - ↑a * -1 * ↑u := by rw [I_mul_I]
      _ = (↑a + ↑E * I) * ↑u := by ring
  have h2 : -I * ((↑E - ↑a * I) * ↑u) =
      -((↑a + ↑E * I) * ↑u) := by
    calc
      -I * ((↑E - ↑a * I) * ↑u)
          = -(I * ((↑E - ↑a * I) * ↑u)) := by ring
      _ = -((↑a + ↑E * I) * ↑u) := by rw [h1]
  have h1' : ((↑E - ↑a * I) * ↑u) * I =
      (↑a + ↑E * I) * ↑u := by
    calc
      ((↑E - ↑a * I) * ↑u) * I =
          I * ((↑E - ↑a * I) * ↑u) := by ring
      _ = (↑a + ↑E * I) * ↑u := h1
  have h2' : -((↑E - ↑a * I) * ↑u) * I =
      -((↑a + ↑E * I) * ↑u) := by
    calc
      -((↑E - ↑a * I) * ↑u) * I =
          -I * ((↑E - ↑a * I) * ↑u) := by ring
      _ = -((↑a + ↑E * I) * ↑u) := h2
  rw [h1', h2']

def RealZeroProperty (H : ℂ → ℂ) : Prop :=
  ∀ z, H z = 0 → z.im = 0

theorem real_spectral_iff_zero_affinity (a E : ℝ) :
    (spectralCoordinate a E).im = 0 ↔ a = 0 := by
  dsimp [spectralCoordinate]
  have h_im : (↑E - ↑a * I).im = -a := by
    simp [Complex.sub_im, Complex.mul_im]
  simpa using (neg_eq_zero : (-a = 0 ↔ a = 0))

noncomputable def RiemannSpectralProbe (s : ℂ) : ℂ :=
  spectralCoordinate (s.re - 1 / 2) s.im

theorem RiemannSpectralProbe_eq_shift (s : ℂ) :
    RiemannSpectralProbe s = -I * (s - 1 / 2) := by
  dsimp [RiemannSpectralProbe, spectralCoordinate]
  apply Complex.ext
  · simp [Complex.mul_re, Complex.sub_re, Complex.mul_im, Complex.sub_im]
  · simp [Complex.mul_re, Complex.sub_re, Complex.mul_im, Complex.sub_im]

theorem RiemannSpectralProbe_eq_zero_iff (s : ℂ) :
    RiemannSpectralProbe s = 0 ↔ s = (1 / 2 : ℂ) := by
  rw [RiemannSpectralProbe_eq_shift]
  constructor
  · intro h
    rcases mul_eq_zero.mp h with hI | hshift
    · norm_num at hI
    · exact sub_eq_zero.mp hshift
  · intro h
    rw [h]
    norm_num

theorem critical_line_iff_real_spectral_probe (s : ℂ) :
    (RiemannSpectralProbe s).im = 0 ↔ s.re = 1 / 2 := by
  rw [RiemannSpectralProbe_eq_shift]
  have h : (-I * (s - 1 / 2)).im = -(s.re - 1 / 2) := by
    simp [Complex.mul_im, Complex.sub_im, Complex.sub_re, Complex.mul_re]
  rw [h]
  constructor <;> intro h_eq <;> linarith

structure DeBruijnNewmanFamily where
  H : ℝ → ℂ → ℂ

def DeBruijnNewmanThreshold (F : DeBruijnNewmanFamily) (Λ : ℝ) : Prop :=
  (∀ t ≥ Λ, RealZeroProperty (F.H t)) ∧
  (∀ t < Λ, ¬ RealZeroProperty (F.H t))

def RiemannHypothesisAtThreshold (F : DeBruijnNewmanFamily) : Prop :=
  DeBruijnNewmanThreshold F 0

end InfoGeometry.Arithmetic.RiemannDeBruijnNewman
