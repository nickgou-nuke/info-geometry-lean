/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic

/-!
# Global cubic and quartic hyperbolic remainder bounds

Checked with Lean 4.34.1 and Mathlib commit d13f23b. The accompanying
verification directory records the actual compiler result for this module.

The inequalities are derived from the actual real hyperbolic functions and
their derivatives. No Taylor remainder, smallness assumption, or desired
analytic inequality is assumed in the public theorem hypotheses.
-/

namespace InfoGeometry.Spectrometry.GlobalHyperbolicBounds

open Set

noncomputable section

theorem hasDerivAt_tanh (x : ℝ) :
    HasDerivAt Real.tanh (1 - Real.tanh x ^ 2) x := by
  have hfun : Real.tanh = fun t => Real.sinh t / Real.cosh t := by
    funext t
    exact Real.tanh_eq_sinh_div_cosh t
  simp only [hfun]
  convert (Real.hasDerivAt_sinh x).div (Real.hasDerivAt_cosh x)
    (Real.cosh_pos x).ne' using 1
  field_simp [(Real.cosh_pos x).ne']

theorem one_sub_tanh_sq (x : ℝ) :
    1 - Real.tanh x ^ 2 = 1 / Real.cosh x ^ 2 := by
  rw [Real.tanh_eq_sinh_div_cosh]
  field_simp [(Real.cosh_pos x).ne']
  nlinarith [Real.cosh_sq_sub_sinh_sq x]

theorem hasDerivAt_tanh_sech (x : ℝ) :
    HasDerivAt Real.tanh (1 / Real.cosh x ^ 2) x := by
  rw [← one_sub_tanh_sq]
  exact hasDerivAt_tanh x

theorem continuous_tanh : Continuous Real.tanh :=
  (show Differentiable ℝ Real.tanh from
    fun x => (hasDerivAt_tanh x).differentiableAt).continuous

theorem strictMono_tanh : StrictMono Real.tanh :=
  strictMono_of_hasDerivAt_pos hasDerivAt_tanh
    (fun x => sub_pos.mpr (Real.tanh_sq_lt_one x))

theorem tanh_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ Real.tanh x := by
  simpa only [Real.tanh_zero] using strictMono_tanh.monotone hx

theorem tanh_nonpos {x : ℝ} (hx : x ≤ 0) : Real.tanh x ≤ 0 := by
  simpa only [Real.tanh_zero] using strictMono_tanh.monotone hx

theorem tanh_le_self {x : ℝ} (hx : 0 ≤ x) : Real.tanh x ≤ x := by
  have hd (t : ℝ) :
      HasDerivAt (fun u => u - Real.tanh u) (Real.tanh t ^ 2) t := by
    convert (hasDerivAt_id t).sub (hasDerivAt_tanh t) using 1 <;>
      first | (funext u; rfl) | ring
  have hm := monotone_of_hasDerivAt_nonneg hd (fun t => sq_nonneg (Real.tanh t))
  have h := hm hx
  simp only [Real.tanh_zero, sub_zero] at h
  linarith

theorem abs_tanh_le_abs (x : ℝ) : |Real.tanh x| ≤ |x| := by
  by_cases hx : 0 ≤ x
  · rw [abs_of_nonneg (tanh_nonneg hx), abs_of_nonneg hx]
    exact tanh_le_self hx
  · have hx' : x ≤ 0 := le_of_lt (lt_of_not_ge hx)
    have h := tanh_le_self (neg_nonneg.mpr hx')
    rw [Real.tanh_neg] at h
    rw [abs_of_nonpos (tanh_nonpos hx'), abs_of_nonpos hx']
    exact h

theorem tanh_sq_le_sq (x : ℝ) : Real.tanh x ^ 2 ≤ x ^ 2 := by
  have habs := abs_tanh_le_abs x
  have hprod := mul_nonneg (sub_nonneg.mpr habs)
    (add_nonneg (abs_nonneg x) (abs_nonneg (Real.tanh x)))
  nlinarith [sq_abs x, sq_abs (Real.tanh x)]

theorem sub_tanh_bounds_nonneg {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ x - Real.tanh x ∧ x - Real.tanh x ≤ x ^ 3 / 3 := by
  have hd (t : ℝ) :
      HasDerivAt (fun u => Real.tanh u - u + u ^ 3 / 3)
        (t ^ 2 - Real.tanh t ^ 2) t := by
    convert ((hasDerivAt_tanh t).sub (hasDerivAt_id t)).add
      (((hasDerivAt_id t).pow 3).div_const 3) using 1 <;> norm_num <;>
      first | (funext u; rfl) | ring
  have hm := monotone_of_hasDerivAt_nonneg hd
    (fun t => sub_nonneg.mpr (tanh_sq_le_sq t))
  have h := hm hx
  norm_num only [Real.tanh_zero, zero_sub, zero_pow, zero_div, zero_add] at h
  exact ⟨sub_nonneg.mpr (tanh_le_self hx), by linarith⟩

/-- A global bound: it requires no restriction on the size of `x`. -/
theorem abs_sub_tanh_le_cube (x : ℝ) :
    |x - Real.tanh x| ≤ |x| ^ 3 / 3 := by
  by_cases hx : 0 ≤ x
  · have h := sub_tanh_bounds_nonneg hx
    rw [abs_of_nonneg h.1, abs_of_nonneg hx]
    exact h.2
  · have hx' : x ≤ 0 := le_of_lt (lt_of_not_ge hx)
    have h := sub_tanh_bounds_nonneg (neg_nonneg.mpr hx')
    have hneg : x - Real.tanh x = -((-x) - Real.tanh (-x)) := by
      rw [Real.tanh_neg]
      ring
    rw [hneg, abs_neg, abs_of_nonneg h.1, abs_of_nonpos hx']
    exact h.2

theorem hasDerivAt_log_cosh (x : ℝ) :
    HasDerivAt (fun t => Real.log (Real.cosh t)) (Real.tanh x) x := by
  simpa only [Real.tanh_eq_sinh_div_cosh] using
    (Real.hasDerivAt_cosh x).log (Real.cosh_pos x).ne'

private theorem nonneg_from_derivative_on_nonnegative
    (f f' : ℝ → ℝ) (hf : ∀ x, HasDerivAt f (f' x) x)
    (hfzero : f 0 = 0) (hderiv : ∀ x, 0 ≤ x → 0 ≤ f' x)
    {x : ℝ} (hx : 0 ≤ x) : 0 ≤ f x := by
  have hcont : Continuous f :=
    (show Differentiable ℝ f from fun t => (hf t).differentiableAt).continuous
  have hm : MonotoneOn f (Ici 0) :=
    monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici _) hcont.continuousOn
      (fun t _ => (hf t).hasDerivWithinAt) (fun t ht => by
        apply hderiv t
        have ht' : 0 < t := by simpa only [interior_Ici, mem_Ioi] using ht
        exact ht'.le)
  have h := hm (show (0 : ℝ) ∈ Ici 0 by simp) hx hx
  simpa only [hfzero] using h

theorem log_cosh_quadratic_bounds_nonneg {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ x ^ 2 / 2 - Real.log (Real.cosh x) ∧
      x ^ 2 / 2 - Real.log (Real.cosh x) ≤ x ^ 4 / 12 := by
  let D : ℝ → ℝ := fun t => t ^ 2 / 2 - Real.log (Real.cosh t)
  have hD (t : ℝ) : HasDerivAt D (t - Real.tanh t) t := by
    dsimp [D]
    convert (((hasDerivAt_id t).pow 2).div_const 2).sub
      (hasDerivAt_log_cosh t) using 1 <;> norm_num
    funext u
    rfl
  have hD0 : D 0 = 0 := by simp [D]
  have hlow : 0 ≤ D x :=
    nonneg_from_derivative_on_nonnegative D _ hD hD0
      (fun t ht => (sub_tanh_bounds_nonneg ht).1) hx
  have hQ (t : ℝ) : HasDerivAt (fun u => u ^ 4 / 12 - D u)
      (t ^ 3 / 3 - (t - Real.tanh t)) t := by
    convert (((hasDerivAt_id t).pow 4).div_const 12).sub (hD t)
      using 1 <;> norm_num <;> first | (funext u; rfl) | ring
  have hhigh : 0 ≤ x ^ 4 / 12 - D x :=
    nonneg_from_derivative_on_nonnegative _ _ hQ (by simp [hD0])
      (fun t ht => sub_nonneg.mpr (sub_tanh_bounds_nonneg ht).2) hx
  change 0 ≤ D x ∧ D x ≤ x ^ 4 / 12
  exact ⟨hlow, by linarith⟩

/-- A global one-sided quartic remainder for `log ∘ cosh`. -/
theorem log_cosh_quadratic_bounds (x : ℝ) :
    0 ≤ x ^ 2 / 2 - Real.log (Real.cosh x) ∧
      x ^ 2 / 2 - Real.log (Real.cosh x) ≤ x ^ 4 / 12 := by
  by_cases hx : 0 ≤ x
  · exact log_cosh_quadratic_bounds_nonneg hx
  · have h := log_cosh_quadratic_bounds_nonneg
      (neg_nonneg.mpr (le_of_lt (lt_of_not_ge hx)))
    simp only [Real.cosh_neg, show (-x) ^ 2 = x ^ 2 by ring,
      show (-x) ^ 4 = x ^ 4 by ring] at h
    exact h

end
end InfoGeometry.Spectrometry.GlobalHyperbolicBounds
