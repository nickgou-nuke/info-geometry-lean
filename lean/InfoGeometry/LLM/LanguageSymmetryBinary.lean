/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Exact logarithmic coordinates for binary attributes

This file formalizes the real logarithm of the factors `1 + s * a * b`
appearing in the binary-attribute model of Karkada et al.,
*Symmetry in language statistics shapes the geometry of model representations*,
arXiv:2602.15029, Appendix D.

A real sign is represented by the native equation `σ ^ 2 = 1`. The two-point
logarithm is affine in that sign. For probabilistic factors, `|s| < 1` proves
strict positivity; no use is made of the totalized value `Real.log 0`.
The finite-product theorem is an identity for an explicitly given kernel.
It does not identify learned embeddings or prove spectral dominance.
-/

noncomputable section

namespace InfoGeometry.LLM.LanguageSymmetry

/-- For positive masses, a zero log ratio expresses equality of the masses.
In particular, replacing a positive joint mass by the product of its positive
marginals makes its PMI zero; setting the joint mass to zero falls outside
these hypotheses. -/
theorem log_ratio_eq_zero_iff {p q : ℝ} (hp : 0 < p) (hq : 0 < q) :
    Real.log (p / q) = 0 ↔ p = q := by
  constructor
  · intro h
    exact (div_eq_one_iff_eq hq.ne').mp
      (Real.eq_one_of_pos_of_log_eq_zero (div_pos hp hq) h)
  · rintro rfl
    rw [div_self hq.ne', Real.log_one]

/-- Mean of the two real logarithmic values at a binary coordinate. -/
def binaryLogMean (s : ℝ) : ℝ :=
  (Real.log (1 + s) + Real.log (1 - s)) / 2

/-- Half of the difference of the logarithmic values at a binary coordinate. -/
def binaryLogContrast (s : ℝ) : ℝ :=
  (Real.log (1 + s) - Real.log (1 - s)) / 2

/-- The two permitted sign values suffice for exact interpolation of the
actual real logarithm. This identity needs no Taylor expansion. -/
theorem binary_log_affine (s σ : ℝ) (hσ : σ ^ 2 = 1) :
    Real.log (1 + s * σ) = binaryLogMean s + binaryLogContrast s * σ := by
  rcases sq_eq_one_iff.mp hσ with rfl | rfl <;>
    simp only [binaryLogMean, binaryLogContrast, mul_one, mul_neg_one,
      ← sub_eq_add_neg] <;> ring

/-- The probabilistic coupling range makes both possible sign factors positive. -/
theorem binary_factor_pos {s σ : ℝ} (hs : |s| < 1) (hσ : σ ^ 2 = 1) :
    0 < 1 + s * σ := by
  rcases abs_lt.mp hs with ⟨hsl, hsu⟩
  rcases sq_eq_one_iff.mp hσ with rfl | rfl <;> linarith

/-- The constant logarithmic coefficient is half the log of `1 - s²`. -/
theorem binaryLogMean_eq_log {s : ℝ} (hs : |s| < 1) :
    binaryLogMean s = Real.log (1 - s ^ 2) / 2 := by
  have hp : 0 < 1 + s := by linarith [(abs_lt.mp hs).1]
  have hm : 0 < 1 - s := sub_pos.mpr (abs_lt.mp hs).2
  rw [binaryLogMean, ← Real.log_mul hp.ne' hm.ne',
    show (1 + s) * (1 - s) = 1 - s ^ 2 by ring]

/-- The sign coefficient is half the log ratio of the two positive factors. -/
theorem binaryLogContrast_eq_log_ratio {s : ℝ} (hs : |s| < 1) :
    binaryLogContrast s = Real.log ((1 + s) / (1 - s)) / 2 := by
  have hp : 0 < 1 + s := by linarith [(abs_lt.mp hs).1]
  have hm : 0 < 1 - s := sub_pos.mpr (abs_lt.mp hs).2
  rw [binaryLogContrast, ← Real.log_div hp.ne' hm.ne']

/-- The usual closed form of the positive binary coupling logarithm. -/
theorem binary_log_affine_closed_form (s σ : ℝ) (hs : |s| < 1)
    (hσ : σ ^ 2 = 1) :
    Real.log (1 + s * σ) = Real.log (1 - s ^ 2) / 2 +
      Real.log ((1 + s) / (1 - s)) / 2 * σ := by
  rw [binary_log_affine s σ hσ, binaryLogMean_eq_log hs,
    binaryLogContrast_eq_log_ratio hs]

/-- Every factor in the finite attribute product lies in the positive real domain. -/
theorem attribute_product_pos {ι : Type*} [Fintype ι]
    (s a b : ι → ℝ) (hs : ∀ r, |s r| < 1)
    (ha : ∀ r, a r ^ 2 = 1) (hb : ∀ r, b r ^ 2 = 1) :
    0 < ∏ r, (1 + s r * (a r * b r)) := by
  apply Finset.prod_pos
  intro r _
  apply binary_factor_pos (hs r)
  rw [mul_pow, ha r, hb r, one_mul]

/-- The logarithm of a multiplicative binary-attribute kernel is exactly a
constant plus a sum of coordinatewise bilinear terms. Positivity is established
from the coupling range, so this is an identity for actual positive factors. -/
theorem log_attribute_product {ι : Type*} [Fintype ι]
    (s a b : ι → ℝ) (hs : ∀ r, |s r| < 1)
    (ha : ∀ r, a r ^ 2 = 1) (hb : ∀ r, b r ^ 2 = 1) :
    Real.log (∏ r, (1 + s r * (a r * b r))) =
      (∑ r, binaryLogMean (s r)) +
        ∑ r, binaryLogContrast (s r) * (a r * b r) := by
  have hab : ∀ r, (a r * b r) ^ 2 = 1 := by
    intro r
    rw [mul_pow, ha r, hb r, one_mul]
  calc
    Real.log (∏ r, (1 + s r * (a r * b r))) =
        ∑ r, Real.log (1 + s r * (a r * b r)) :=
      Real.log_prod (fun r _ => (binary_factor_pos (hs r) (hab r)).ne')
    _ = ∑ r, (binaryLogMean (s r) +
        binaryLogContrast (s r) * (a r * b r)) := by
      apply Finset.sum_congr rfl
      intro r _
      exact binary_log_affine (s r) (a r * b r) (hab r)
    _ = _ := Finset.sum_add_distrib

end InfoGeometry.LLM.LanguageSymmetry
