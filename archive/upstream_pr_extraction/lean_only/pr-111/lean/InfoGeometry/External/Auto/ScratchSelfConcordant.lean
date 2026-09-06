import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.Deriv.ZPow
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Positivity

open Real

theorem neg_log_deriv1 (x : ℝ) (hx : x ≠ 0) :
    HasDerivAt (fun y => - Real.log y) (- x⁻¹) x :=
  (hasDerivAt_log hx).neg

theorem neg_inv_deriv (x : ℝ) (hx : x ≠ 0) :
    HasDerivAt (fun y : ℝ => - y⁻¹) (x ^ (-2 : ℤ)) x := by
  have h1 : HasDerivAt (fun y : ℝ => y⁻¹) (-(x ^ 2)⁻¹) x := hasDerivAt_inv hx
  have h2 : HasDerivAt (fun y : ℝ => - y⁻¹) (-(-(x ^ 2)⁻¹)) x := h1.neg
  have h3 : -(-(x ^ 2)⁻¹) = x ^ (-2 : ℤ) := by
    simp only [neg_neg]
    rfl
  rwa [h3] at h2

theorem zpow_neg_two_deriv (x : ℝ) (hx : x ≠ 0) :
    HasDerivAt (fun y : ℝ => y ^ (-2 : ℤ)) (-2 * x ^ (-3 : ℤ)) x := by
  have h1 := hasDerivAt_zpow (-2 : ℤ) x (Or.inl hx)
  have h2 : (↑(-2 : ℤ) : ℝ) * x ^ (-2 - 1 : ℤ) = -2 * x ^ (-3 : ℤ) := by
    norm_cast
  rwa [h2] at h1

theorem neg_log_self_concordant_proof (x : ℝ) (hx : 0 < x) :
    abs (deriv (deriv (deriv (fun y => - Real.log y))) x) ≤
      2 * (deriv (deriv (fun y => - Real.log y)) x) ^ (3 / 2 : ℝ) := by
  have hx_ne : x ≠ 0 := ne_of_gt hx
  
  -- 1st deriv
  have d1 : ∀ᶠ y in nhds x, deriv (fun z => - Real.log z) y = - y⁻¹ := by
    filter_upwards [eventually_ne_nhds hx_ne] with y hy
    exact (neg_log_deriv1 y hy).deriv
  
  -- 2nd deriv
  have d2_at : HasDerivAt (fun y => deriv (fun z => - Real.log z) y) (x ^ (-2 : ℤ)) x := by
    apply HasDerivAt.congr_of_eventuallyEq (neg_inv_deriv x hx_ne) d1
  have d2_eq : deriv (deriv (fun y => - Real.log y)) x = x ^ (-2 : ℤ) := d2_at.deriv
  
  -- 2nd deriv local eq
  have d2 : ∀ᶠ y in nhds x, deriv (deriv (fun z => - Real.log z)) y = y ^ (-2 : ℤ) := by
    filter_upwards [eventually_ne_nhds hx_ne] with y hy
    have d1_y : ∀ᶠ z in nhds y, deriv (fun w => - Real.log w) z = - z⁻¹ := by
      filter_upwards [eventually_ne_nhds hy] with z hz
      exact (neg_log_deriv1 z hz).deriv
    exact (HasDerivAt.congr_of_eventuallyEq (neg_inv_deriv y hy) d1_y).deriv
    
  -- 3rd deriv
  have d3_at : HasDerivAt (fun y => deriv (deriv (fun z => - Real.log z)) y) (-2 * x ^ (-3 : ℤ)) x := by
    apply HasDerivAt.congr_of_eventuallyEq (zpow_neg_two_deriv x hx_ne) d2
  have d3_eq : deriv (deriv (deriv (fun y => - Real.log y))) x = -2 * x ^ (-3 : ℤ) := d3_at.deriv

  rw [d2_eq, d3_eq]
  
  -- Now algebraic inequality: abs (-2 * x ^ -3) ≤ 2 * (x ^ -2) ^ (3/2)
  have h_rpow : (x ^ (-2 : ℤ)) ^ (3 / 2 : ℝ) = x ^ (-3 : ℤ) := by
    rw [← Real.rpow_intCast]
    rw [← Real.rpow_mul (le_of_lt hx)]
    have h_mul : (-2 : ℝ) * (3 / 2 : ℝ) = -3 := by norm_num
    have h_mul2 : (↑(-2 : ℤ) : ℝ) * (3 / 2 : ℝ) = -3 := by
      push_cast
      exact h_mul
    rw [h_mul2]
    simp
  rw [h_rpow]
  have h_pos : (0 : ℝ) < x ^ (-3 : ℤ) := by positivity
  have h_abs : abs (-2 * x ^ (-3 : ℤ)) = 2 * x ^ (-3 : ℤ) := by
    have : -2 * x ^ (-3 : ℤ) < 0 := by
      apply mul_neg_of_neg_of_pos
      norm_num
      exact h_pos
    rw [abs_of_neg this]
    ring
  rw [h_abs]
