import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

/-!
# Finite Amari dual coordinates on the complexified one-simplex

This owner contains the algebraic coordinate identities for
`τ = s / (1 - s)`, the Fisher polynomial `s(1-s)`, and the real simplex
deviance about `1/2`.  It does not assert an RH theorem, a global logarithm
branch, or an analytic Euler-product identity.
-/

noncomputable section

namespace InfoGeometry.Arithmetic.AmariZeta

open Complex

def mCoord (s : ℂ) : ℂ := s

def fugacityTau (s : ℂ) : ℂ := s / (1 - s)

def fromFugacity (τ : ℂ) : ℂ := τ / (1 + τ)

@[simp] theorem fromFugacity_fugacityTau (s : ℂ) (hs : 1 - s ≠ 0) :
    fromFugacity (fugacityTau s) = s := by
  unfold fromFugacity fugacityTau
  have h1 : 1 + s / (1 - s) = 1 / (1 - s) := by
    calc
      1 + s / (1 - s) = (1 - s) / (1 - s) + s / (1 - s) := by
        rw [div_self hs]
      _ = ((1 - s) + s) / (1 - s) := by rw [add_div]
      _ = 1 / (1 - s) := by ring
  rw [h1]
  field_simp [hs]

@[simp] theorem fugacityTau_one_sub (s : ℂ) :
    fugacityTau (1 - s) = (fugacityTau s)⁻¹ := by
  unfold fugacityTau
  rw [show 1 - (1 - s) = s by ring, inv_div]

def fisherRaoMetric (s : ℂ) : ℂ := s * (1 - s)

theorem fisherRaoMetric_on_critical_line (t : ℝ) :
    fisherRaoMetric ((1 / 2 : ℂ) + I * (t : ℂ)) =
      ((1 / 4 : ℝ) + t ^ 2 : ℂ) := by
  unfold fisherRaoMetric
  have hsub : 1 - ((1 / 2 : ℂ) + I * (t : ℂ)) =
      (1 / 2 : ℂ) - I * (t : ℂ) := by ring
  rw [hsub]
  rw [show ((1 / 2 : ℂ) + I * (t : ℂ)) *
      ((1 / 2 : ℂ) - I * (t : ℂ)) =
        (1 / 2 : ℂ) ^ 2 - (I * (t : ℂ)) ^ 2 by ring]
  rw [show (I * (t : ℂ)) ^ 2 = I ^ 2 * (t : ℂ) ^ 2 by ring, I_sq]
  push_cast
  ring

theorem fisherRaoMetric_on_critical_line_pos (t : ℝ) :
    0 < (1 / 4 : ℝ) + t ^ 2 := by
  nlinarith [sq_nonneg t]

theorem fisherRaoMetric_is_real_iff (s : ℂ) :
    (fisherRaoMetric s).im = 0 ↔ s.re = 1 / 2 ∨ s.im = 0 := by
  unfold fisherRaoMetric
  have him : (s * (1 - s)).im = s.im * (1 - 2 * s.re) := by
    simp only [mul_im, one_re, one_im, sub_re, sub_im]
    ring
  rw [him, mul_eq_zero]
  constructor
  · rintro (h | h)
    · right
      exact h
    · left
      linarith
  · rintro (h | h)
    · right
      linarith
    · left
      exact h

theorem normSq_fugacityTau_eq_one_iff (s : ℂ) (hs : 1 - s ≠ 0) :
    Complex.normSq (fugacityTau s) = 1 ↔ s.re = 1 / 2 := by
  unfold fugacityTau
  rw [Complex.normSq_div]
  have hzero : Complex.normSq (1 - s) ≠ 0 := by
    intro h
    exact hs (Complex.normSq_eq_zero.mp h)
  rw [div_eq_one_iff_eq hzero]
  constructor
  · intro h
    simp [Complex.normSq_apply] at h
    nlinarith [h]
  · intro h
    simp [Complex.normSq_apply]
    nlinarith [h]

def amariDevianceFromSeam (s : ℝ) : ℝ :=
  Real.log 2 + s * Real.log s + (1 - s) * Real.log (1 - s)

@[simp] theorem amariDeviance_seam_zero :
    amariDevianceFromSeam (1 / 2) = 0 := by
  unfold amariDevianceFromSeam
  have hhalf : 1 - (1 / 2 : ℝ) = 1 / 2 := by ring
  rw [hhalf]
  have hlog : Real.log (1 / 2 : ℝ) = -Real.log 2 := by
    rw [Real.log_div (by norm_num) (by norm_num), Real.log_one, zero_sub]
  rw [hlog]
  ring

theorem amariDeviance_reflection (s : ℝ) :
    amariDevianceFromSeam (1 - s) = amariDevianceFromSeam s := by
  unfold amariDevianceFromSeam
  rw [show 1 - (1 - s) = s by ring]
  ring

end InfoGeometry.Arithmetic.AmariZeta
