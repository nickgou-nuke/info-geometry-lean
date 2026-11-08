import Mathlib.Analysis.Complex.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Tactic

/-!
# Actual critical-line polar readout of Mathlib `riemannZeta`

This owner separates the actual critical-line zeta value into its norm and
principal argument.  The polar reconstruction is conditional away from a
zero, as it must be.  The argument is the principal `Complex.arg`; no claim is
made that it is the Riemann--Siegel theta function, and no global oddness or
Hardy-Z identification is asserted.
-/

noncomputable section

namespace InfoGeometry.Canonical.ActualCriticalLineZetaPolarReadout

open Complex

def actualCriticalLineZeta (t : ℝ) : ℂ :=
  riemannZeta ((1 / 2 : ℂ) + Complex.I * (t : ℂ))

def actualCriticalLineAmplitude (t : ℝ) : ℝ :=
  ‖actualCriticalLineZeta t‖

def actualCriticalLinePhase (t : ℝ) : ℝ :=
  Complex.arg (actualCriticalLineZeta t)

@[simp] theorem actualCriticalLineAmplitude_nonnegative (t : ℝ) :
    0 ≤ actualCriticalLineAmplitude t := by
  exact norm_nonneg _

theorem actualCriticalLineZeta_normSq_eq_amplitude_sq (t : ℝ) :
    Complex.normSq (actualCriticalLineZeta t) =
      (actualCriticalLineAmplitude t) ^ 2 := by
  rw [Complex.normSq_eq_norm_sq]
  rfl

theorem actualCriticalLineZeta_polar_reconstruction
    (t : ℝ) (ht : actualCriticalLineZeta t ≠ 0) :
    actualCriticalLineZeta t =
      (actualCriticalLineAmplitude t : ℂ) *
        Complex.exp ((actualCriticalLinePhase t : ℂ) * Complex.I) := by
  have hnorm : ‖actualCriticalLineZeta t‖ ≠ 0 :=
    (norm_pos_iff.mpr ht).ne'
  change actualCriticalLineZeta t =
    (‖actualCriticalLineZeta t‖ : ℂ) *
      Complex.exp ((Complex.arg (actualCriticalLineZeta t) : ℂ) * Complex.I)
  apply Complex.ext
  · rw [Complex.mul_re, Complex.exp_mul_I]
    rw [← Complex.ofReal_cos, ← Complex.ofReal_sin]
    simp only [Complex.ofReal_re, Complex.ofReal_im, Complex.add_re,
      Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]
    rw [Complex.cos_arg ht]
    field_simp [hnorm]
    ring
  · rw [Complex.mul_im, Complex.exp_mul_I]
    rw [← Complex.ofReal_cos, ← Complex.ofReal_sin]
    simp only [Complex.ofReal_re, Complex.ofReal_im, Complex.add_im,
      Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]
    rw [Complex.sin_arg]
    field_simp [hnorm]
    ring

theorem actualCriticalLineZeta_zero_iff_amplitude_zero (t : ℝ) :
    actualCriticalLineZeta t = 0 ↔ actualCriticalLineAmplitude t = 0 := by
  unfold actualCriticalLineAmplitude
  constructor
  · intro h
    simp [h]
  · exact norm_eq_zero.mp

end InfoGeometry.Canonical.ActualCriticalLineZetaPolarReadout
