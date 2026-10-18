/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Tactic.Ring
import InfoGeometry.QuantumContext.SorkinBornRuleSuperposedABFluxQubit

/-!
# Section 120b: Additional Identities for the Canonical Fresnel Wave

This module extends the existing `SorkinFluxQubit.FresnelWave` owner. It adds
quadrature pairing, sum-of-squares, equal-input, and ordered-ring lemmas without
introducing a second Fresnel carrier or redefining its intensity and transition
expression.
-/

namespace InfoGeometry.QuantumContext.SorkinFluxQubit.FresnelWave

variable {R : Type*} [CommRing R]

/-- The Yang pairing is symmetric in its two Fresnel waves. -/
@[simp]
theorem yang_symmetric_under_slit_swap (ψ₁ ψ₂ : FresnelWave R) :
    yangG ψ₂ ψ₁ = yangG ψ₁ ψ₂ := by
  dsimp [yangG]
  ring

/-- The Yin pairing changes sign when its two Fresnel waves are swapped. -/
@[simp]
theorem yin_skew_symmetric_under_slit_swap (ψ₁ ψ₂ : FresnelWave R) :
    yinH ψ₂ ψ₁ = - yinH ψ₁ ψ₂ := by
  dsimp [yinH]
  ring

/-- The alternating Yin pairing vanishes on equal inputs. -/
@[simp]
theorem yin_zero_on_equal_inputs (ψ : FresnelWave R) : yinH ψ ψ = 0 := by
  dsimp [yinH]
  ring

/-- On equal inputs the Yang pairing equals the intensity. -/
@[simp]
theorem yang_eq_intensity_on_equal_inputs (ψ : FresnelWave R) :
    yangG ψ ψ = intensity ψ := by
  dsimp [yangG, intensity]

/-- The product of the two intensities is the sum of squared Yang and Yin pairings. -/
theorem brahmagupta_fibonacci_fresnel_norm_identity (ψ₁ ψ₂ : FresnelWave R) :
    intensity ψ₁ * intensity ψ₂ =
      yangG ψ₁ ψ₂ * yangG ψ₁ ψ₂ + yinH ψ₁ ψ₂ * yinH ψ₁ ψ₂ := by
  dsimp [intensity, yangG, yinH]
  ring

/-- The canonical Sorkin-owner transition expression is a sum of two squares. -/
theorem ab_probability_plus_sum_of_squares (ψ₁ ψ₂ : FresnelWave R) (c s : R) :
    abProb ψ₁ ψ₂ c s =
      (ψ₁.cQuad + c * ψ₂.cQuad + s * ψ₂.sQuad) *
        (ψ₁.cQuad + c * ψ₂.cQuad + s * ψ₂.sQuad) +
      (ψ₁.sQuad - s * ψ₂.cQuad + c * ψ₂.sQuad) *
        (ψ₁.sQuad - s * ψ₂.cQuad + c * ψ₂.sQuad) := by
  dsimp [abProb, intensity, yangG, yinH]
  ring

/-- Reversing the supplied second parameter gives the corresponding signed sum of squares. -/
theorem ab_probability_minus_sum_of_squares (ψ₁ ψ₂ : FresnelWave R) (c s : R) :
    abProb ψ₁ ψ₂ c (-s) =
      (ψ₁.cQuad + c * ψ₂.cQuad - s * ψ₂.sQuad) *
        (ψ₁.cQuad + c * ψ₂.cQuad - s * ψ₂.sQuad) +
      (ψ₁.sQuad + s * ψ₂.cQuad + c * ψ₂.sQuad) *
        (ψ₁.sQuad + s * ψ₂.cQuad + c * ψ₂.sQuad) := by
  dsimp [abProb, intensity, yangG, yinH]
  ring

/-- For equal waves and parameters `(c,s)=(1,0)`, the transition expression is four times intensity. -/
theorem equal_input_plus_expression_at_one_zero_eq_four_intensity (ψ : FresnelWave R) :
    abProb ψ ψ 1 0 = 4 * intensity ψ := by
  dsimp [abProb, intensity, yangG, yinH]
  ring

/-- For equal waves and parameters `(c,s)=(-1,0)`, the transition expression vanishes. -/
theorem equal_input_plus_expression_at_neg_one_zero_eq_zero (ψ : FresnelWave R) :
    abProb ψ ψ (-1) 0 = 0 := by
  dsimp [abProb, intensity, yangG, yinH]
  ring

/-- At `(c,s)=(-1,0)`, the transition expression is the squared coordinate difference. -/
theorem plus_expression_neg_one_zero_eq_difference_squares (ψ₁ ψ₂ : FresnelWave R) :
    abProb ψ₁ ψ₂ (-1) 0 =
      (ψ₁.cQuad - ψ₂.cQuad) * (ψ₁.cQuad - ψ₂.cQuad) +
      (ψ₁.sQuad - ψ₂.sQuad) * (ψ₁.sQuad - ψ₂.sQuad) := by
  dsimp [abProb, intensity, yangG, yinH]
  ring

/-- For equal waves and `(c,s)=(0,±1)`, the transition expression is twice intensity. -/
theorem equal_input_plus_expression_at_zero_pm_one_eq_two_intensity (ψ : FresnelWave R) :
    abProb ψ ψ 0 1 = 2 * intensity ψ ∧
    abProb ψ ψ 0 (-1) = 2 * intensity ψ := by
  constructor <;> dsimp [abProb, intensity, yangG, yinH] <;> ring

section OrderedRing

variable {K : Type*} [CommRing K] [LinearOrder K] [IsStrictOrderedRing K]

/-- The canonical transition expression is nonnegative over an ordered commutative ring. -/
theorem ab_probability_plus_nonneg (ψ₁ ψ₂ : FresnelWave K) (c s : K) :
    0 ≤ abProb ψ₁ ψ₂ c s := by
  rw [ab_probability_plus_sum_of_squares]
  exact add_nonneg (mul_self_nonneg _) (mul_self_nonneg _)

/-- The transition expression with the second parameter negated is nonnegative. -/
theorem ab_probability_minus_nonneg (ψ₁ ψ₂ : FresnelWave K) (c s : K) :
    0 ≤ abProb ψ₁ ψ₂ c (-s) := by
  rw [ab_probability_minus_sum_of_squares]
  exact add_nonneg (mul_self_nonneg _) (mul_self_nonneg _)

/-- A supplied scalar expression is negative exactly under the equivalent strict inequality. -/
theorem asymptotic_truncation_negative_prob_iff (I₁ I₂ H : K) :
    I₁ + I₂ - 2 * H < 0 ↔ I₁ + I₂ < 2 * H :=
  sub_neg

end OrderedRing

end InfoGeometry.QuantumContext.SorkinFluxQubit.FresnelWave
