/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Spectrometry.ExactTwoLineRoot
import Mathlib.Tactic

/-!
# Nonasymptotic two-line root and centered sample bounds

Checked with Lean 4.34.1 and Mathlib commit d13f23b. Companion files
`GlobalHyperbolicBounds.lean` and `ExactTwoLineRoot.lean` must be on the import
path. The analytic estimates below are derived from their actual hyperbolic
function theorems, not supplied as remainder hypotheses.

The centered sample bound holds for every real shift. Its sharper constant
uses the one-sided range of the log-cosh remainder: centering a function whose
range lies in an interval of length H costs H, not 2H.
-/

namespace InfoGeometry.Spectrometry.TwoLineNonasymptoticBounds

open Set
open scoped BigOperators
open GlobalHyperbolicBounds ExactTwoLineRoot

noncomputable section

variable {J : Type*} [Fintype J] [Nonempty J]

theorem scoreDerivative_upper_bound (z : J → ℝ) (M : ℝ) (hM : 0 ≤ M)
    (hbound : ∀ j, |z j| ≤ M) (t : ℝ) (ht : |t| ≤ 2 * M) :
    scoreDerivative z t ≤ -(Fintype.card J : ℝ) / (2 * Real.cosh (2 * M) ^ 2) := by
  have hterm (j : J) :
      -(1 / Real.cosh (z j - t / 2) ^ 2) / 2 ≤
        -(1 / Real.cosh (2 * M) ^ 2) / 2 := by
    have hz := abs_le.mp (hbound j)
    have ht' := abs_le.mp ht
    have hx : |z j - t / 2| ≤ 2 * M :=
      abs_le.mpr ⟨by linarith [hz.1, ht'.2], by linarith [hz.2, ht'.1]⟩
    have hc : Real.cosh (z j - t / 2) ≤ Real.cosh (2 * M) := by
      apply Real.cosh_le_cosh.mpr
      simpa only [abs_of_nonneg (by linarith only [hM] : 0 ≤ 2 * M)] using hx
    have hsq : Real.cosh (z j - t / 2) ^ 2 ≤ Real.cosh (2 * M) ^ 2 := by
      nlinarith [Real.cosh_pos (z j - t / 2), Real.cosh_pos (2 * M)]
    have hinv : 1 / Real.cosh (2 * M) ^ 2 ≤
        1 / Real.cosh (z j - t / 2) ^ 2 := by
      apply (div_le_div_iff₀ (pow_pos (Real.cosh_pos (2 * M)) 2)
        (pow_pos (Real.cosh_pos (z j - t / 2)) 2)).mpr
      simpa only [one_mul] using hsq
    linarith
  calc
    scoreDerivative z t = ∑ j, -(1 / Real.cosh (z j - t / 2) ^ 2) / 2 := rfl
    _ ≤ ∑ _j : J, -(1 / Real.cosh (2 * M) ^ 2) / 2 :=
      Finset.sum_le_sum (fun j _ => hterm j)
    _ = -(Fintype.card J : ℝ) / (2 * Real.cosh (2 * M) ^ 2) := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      field_simp [(Real.cosh_pos (2 * M)).ne']

/-- Cubic moment bound for the unique exact root, with no smallness condition. -/
theorem root_abs_le_cubic_moment (z : J → ℝ) (M : ℝ) (hM : 0 ≤ M)
    (hbound : ∀ j, |z j| ≤ M) (hcenter : ∑ j, z j = 0)
    (delta : ℝ) (hzero : score z delta = 0) :
    |delta| ≤ (2 * Real.cosh (2 * M) ^ 2 / (3 * (Fintype.card J : ℝ))) *
      ∑ j, |z j| ^ 3 := by
  let A : ℝ := (Fintype.card J : ℝ) / (2 * Real.cosh (2 * M) ^ 2)
  have hn : 0 < (Fintype.card J : ℝ) := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card J)
  have hA : 0 < A := div_pos hn (mul_pos (by norm_num)
    (pow_pos (Real.cosh_pos (2 * M)) 2))
  have hdiff : Differentiable ℝ (score z) :=
    fun t => (hasDerivAt_score z t).differentiableAt
  have hderiv : ∀ t ∈ interior (Icc (-(2 * M)) (2 * M)), deriv (score z) t ≤ -A := by
    intro t ht
    have ht' : t ∈ Icc (-(2 * M)) (2 * M) := interior_subset ht
    rw [(hasDerivAt_score z t).deriv]
    simpa only [A, neg_div] using
      scoreDerivative_upper_bound z M hM hbound t (abs_le.mpr ht')
  have hsec (a : ℝ) (ha : a ∈ Icc (-(2 * M)) (2 * M))
      (b : ℝ) (hb : b ∈ Icc (-(2 * M)) (2 * M)) (hab : a ≤ b) :
      score z b - score z a ≤ (-A) * (b - a) :=
    (convex_Icc (-(2 * M)) (2 * M)).image_sub_le_mul_sub_of_deriv_le
      (continuous_score z).continuousOn hdiff.differentiableOn hderiv a ha b hb hab
  have hdelta := abs_le.mp (root_abs_le z M hM hbound delta hzero)
  have h0 : (0 : ℝ) ∈ Icc (-(2 * M)) (2 * M) := ⟨by linarith, by linarith⟩
  have hresidual := abs_score_zero_le_cubic z hcenter
  have hweighted : A * |delta| ≤ (∑ j, |z j| ^ 3) / 3 := by
    by_cases hd : 0 ≤ delta
    · have hs := hsec 0 h0 delta hdelta hd
      rw [hzero] at hs
      rw [abs_of_nonneg hd]
      nlinarith [le_abs_self (score z 0)]
    · have hd' : delta ≤ 0 := le_of_lt (lt_of_not_ge hd)
      have hs := hsec delta hdelta 0 h0 hd'
      rw [hzero] at hs
      rw [abs_of_nonpos hd']
      nlinarith [neg_le_abs (score z 0)]
  calc
    |delta| ≤ ((∑ j, |z j| ^ 3) / 3) / A :=
      (le_div_iff₀ hA).mpr (by simpa only [mul_comm] using hweighted)
    _ = (2 * Real.cosh (2 * M) ^ 2 / (3 * (Fintype.card J : ℝ))) *
        ∑ j, |z j| ^ 3 := by
      dsimp [A]
      field_simp [hn.ne', (Real.cosh_pos (2 * M)).ne']

/-- The max-only cubic estimate follows by bounding every cubic moment by M³. -/
theorem root_abs_le_cubic_max (z : J → ℝ) (M : ℝ) (hM : 0 ≤ M)
    (hbound : ∀ j, |z j| ≤ M) (hcenter : ∑ j, z j = 0)
    (delta : ℝ) (hzero : score z delta = 0) :
    |delta| ≤ (2 / 3 : ℝ) * Real.cosh (2 * M) ^ 2 * M ^ 3 := by
  have hn : 0 < (Fintype.card J : ℝ) := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card J)
  have hpow (j : J) : |z j| ^ 3 ≤ M ^ 3 := by
    have hj := hbound j
    gcongr
  have hmom : (∑ j, |z j| ^ 3) ≤ (Fintype.card J : ℝ) * M ^ 3 := by
    calc
      (∑ j, |z j| ^ 3) ≤ ∑ _j : J, M ^ 3 := Finset.sum_le_sum (fun j _ => hpow j)
      _ = (Fintype.card J : ℝ) * M ^ 3 := by
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hfactor : 0 ≤ 2 * Real.cosh (2 * M) ^ 2 / (3 * (Fintype.card J : ℝ)) := by
    positivity
  calc
    |delta| ≤ (2 * Real.cosh (2 * M) ^ 2 / (3 * (Fintype.card J : ℝ))) *
        ∑ j, |z j| ^ 3 := root_abs_le_cubic_moment z M hM hbound hcenter delta hzero
    _ ≤ (2 * Real.cosh (2 * M) ^ 2 / (3 * (Fintype.card J : ℝ))) *
        ((Fintype.card J : ℝ) * M ^ 3) := mul_le_mul_of_nonneg_left hmom hfactor
    _ = (2 / 3 : ℝ) * Real.cosh (2 * M) ^ 2 * M ^ 3 := by
      field_simp [hn.ne']

def center (f : J → ℝ) (j : J) : ℝ :=
  f j - (∑ k, f k) / (Fintype.card J : ℝ)

/-- Centering costs the interval width, not twice that width. -/
theorem abs_center_le_range (f : J → ℝ) (a b : ℝ)
    (hf : ∀ j, a ≤ f j ∧ f j ≤ b) (j : J) : |center f j| ≤ b - a := by
  have hn : 0 < (Fintype.card J : ℝ) := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card J)
  have hsumlo : (Fintype.card J : ℝ) * a ≤ ∑ k, f k := by
    simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] using
      Finset.sum_le_sum (fun k (_ : k ∈ (Finset.univ : Finset J)) => (hf k).1)
  have hsumhi : (∑ k, f k) ≤ (Fintype.card J : ℝ) * b := by
    simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] using
      Finset.sum_le_sum (fun k (_ : k ∈ (Finset.univ : Finset J)) => (hf k).2)
  have havglo : a ≤ (∑ k, f k) / (Fintype.card J : ℝ) :=
    (le_div_iff₀ hn).mpr (by simpa only [mul_comm] using hsumlo)
  have havghi : (∑ k, f k) / (Fintype.card J : ℝ) ≤ b :=
    (div_le_iff₀ hn).mpr (by simpa only [mul_comm] using hsumhi)
  unfold center
  apply abs_le.mpr
  constructor <;> linarith [(hf j).1, (hf j).2]

def quadraticRemainder (x : ℝ) : ℝ :=
  Real.log (Real.cosh x) - x ^ 2 / 2

theorem centered_quadratic_shift (z : J → ℝ) (delta : ℝ)
    (hcenter : ∑ j, z j = 0) (j : J) :
    center (fun k => Real.log (Real.cosh (z k - delta / 2)) - z k ^ 2 / 2) j =
      center (fun k => quadraticRemainder (z k - delta / 2)) j - (delta / 2) * z j := by
  have hn : (Fintype.card J : ℝ) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card J ≠ 0)
  have hfun : (fun k => Real.log (Real.cosh (z k - delta / 2)) - z k ^ 2 / 2) =
      (fun k => quadraticRemainder (z k - delta / 2) - (delta / 2) * z k + delta ^ 2 / 8) := by
    funext k
    unfold quadraticRemainder
    ring
  rw [hfun]
  simp only [center, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.mul_sum, hcenter, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  field_simp [hn]
  ring

/-- The uniform centered quadratic approximation bound. The shift need not be
a root; applying the preceding root theorem gives a fully a priori bound. -/
theorem centered_log_cosh_error (z : J → ℝ) (M : ℝ) (hM : 0 ≤ M)
    (hbound : ∀ j, |z j| ≤ M) (hcenter : ∑ j, z j = 0) (delta : ℝ) (j : J) :
    |center (fun k => Real.log (Real.cosh (z k - delta / 2)) - z k ^ 2 / 2) j| ≤
      (|delta| / 2) * M + (M + |delta| / 2) ^ 4 / 12 := by
  let a : ℝ := M + |delta| / 2
  let H : ℝ := a ^ 4 / 12
  have ha : 0 ≤ a := add_nonneg hM (div_nonneg (abs_nonneg delta) (by norm_num))
  have hrange (k : J) :
      -H ≤ quadraticRemainder (z k - delta / 2) ∧
        quadraticRemainder (z k - delta / 2) ≤ 0 := by
    have hz := abs_le.mp (hbound k)
    have hx : |z k - delta / 2| ≤ a := by
      apply abs_le.mpr
      dsimp [a]
      constructor <;> linarith [neg_le_abs delta, le_abs_self delta, hz.1, hz.2]
    have hp : (z k - delta / 2) ^ 4 ≤ a ^ 4 := by
      calc
        (z k - delta / 2) ^ 4 = |z k - delta / 2| ^ 4 := by
          rw [← abs_pow, abs_of_nonneg (by positivity : 0 ≤ (z k - delta / 2) ^ 4)]
        _ ≤ a ^ 4 := by gcongr
    have hb := log_cosh_quadratic_bounds (z k - delta / 2)
    dsimp [quadraticRemainder, H]
    constructor <;> nlinarith [hb.1, hb.2]
  have hcenterR : |center (fun k => quadraticRemainder (z k - delta / 2)) j| ≤ H := by
    simpa only [sub_neg_eq_add, zero_add] using
      abs_center_le_range (fun k => quadraticRemainder (z k - delta / 2)) (-H) 0 hrange j
  have hlinear : |(delta / 2) * z j| ≤ (|delta| / 2) * M := by
    simpa only [abs_mul, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)] using
      mul_le_mul_of_nonneg_left (hbound j)
        (div_nonneg (abs_nonneg delta) (by norm_num : (0 : ℝ) ≤ 2))
  rw [centered_quadratic_shift z delta hcenter j]
  calc
    |center (fun k => quadraticRemainder (z k - delta / 2)) j - (delta / 2) * z j| ≤
        |center (fun k => quadraticRemainder (z k - delta / 2)) j| + |(delta / 2) * z j| :=
      by simpa only [sub_zero, zero_sub, abs_neg] using
        abs_sub_le (center (fun k => quadraticRemainder (z k - delta / 2)) j)
          0 ((delta / 2) * z j)
    _ ≤ H + (|delta| / 2) * M := add_le_add hcenterR hlinear
    _ = (|delta| / 2) * M + (M + |delta| / 2) ^ 4 / 12 := by dsimp [H, a]; ring

end
end InfoGeometry.Spectrometry.TwoLineNonasymptoticBounds
