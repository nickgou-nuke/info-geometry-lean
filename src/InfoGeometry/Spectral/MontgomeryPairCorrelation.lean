import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Data.Complex.Basic
import Mathlib.Topology.Instances.Complex
import Mathlib.Tactic

namespace InfoGeometry.Spectral.MontgomeryPairCorrelation

open Complex Real

noncomputable section

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

def montgomeryPairCorrelation (s : ℝ) : ℝ :=
  if s = 0 then 0 else 1 - (Real.sin (Real.pi * s) / (Real.pi * s)) ^ 2

theorem montgomery_at_zero :
    montgomeryPairCorrelation 0 = 0 := by
  unfold montgomeryPairCorrelation
  simp

theorem montgomery_even (s : ℝ) :
    montgomeryPairCorrelation (-s) = montgomeryPairCorrelation s := by
  unfold montgomeryPairCorrelation
  by_cases hs : s = 0
  · simp [hs]
  · have h_neg : -s ≠ 0 := neg_ne_zero.mpr hs
    simp only [hs, h_neg, if_false]
    have h_sin : Real.sin (Real.pi * -s) = - Real.sin (Real.pi * s) := by
      have : Real.pi * -s = - (Real.pi * s) := by ring
      rw [this, Real.sin_neg]
    have h_den : Real.pi * -s = - (Real.pi * s) := by ring
    rw [h_sin, h_den, neg_div_neg_eq]

theorem montgomery_at_integer (k : ℤ) (hk : k ≠ 0) :
    montgomeryPairCorrelation (k : ℝ) = 1 := by
  unfold montgomeryPairCorrelation
  have hk_real : (k : ℝ) ≠ 0 := by exact_mod_cast hk
  simp only [hk_real, if_false]
  have h_sin : Real.sin (Real.pi * (k : ℝ)) = 0 := by
    rw [mul_comm, Real.sin_int_mul_pi]
  rw [h_sin, zero_div, sq (0 : ℝ), mul_zero, sub_zero]
