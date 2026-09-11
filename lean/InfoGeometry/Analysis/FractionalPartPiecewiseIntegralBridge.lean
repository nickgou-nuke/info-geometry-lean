import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic

/-!
# Exact Fractional Part Piecewise Interval Integral Bridge

This module formalizes genuine Lebesgue interval integrals for the fractional part kernel $\{1/x\}$ in Mathlib 4:
1. **Exact Cell Integral of $1/x - k$ on $[1/(k+1), 1/k]$**:
   $$\int_{1/(k+1)}^{1/k} \left(\frac{1}{x} - k\right) dx = \ln(k+1) - \ln(k) - \frac{1}{k+1} \quad (\forall k \ge 1)$$
2. **Exact Telescoping Logarithmic Sum Identity**:
   $$\sum_{k=0}^{N-1} (\ln(k+2) - \ln(k+1)) = \ln(N+1)$$
3. **Exact Master Cell-Sum Formula for Fractional Part Integrals**:
   $$\sum_{k=0}^{N-1} \left(\ln(k+2) - \ln(k+1) - \frac{1}{k+2}\right) = \ln(N+1) - \sum_{k=0}^{N-1} \frac{1}{k+2}$$
-/

noncomputable section

namespace InfoGeometry.Analysis.FractionalPart

open Real intervalIntegral Finset MeasureTheory

/-- 🏆 THEOREM 1: Exact Cell Integral of 1/x - k on [1/(k+1), 1/k] -/
theorem cell_fractional_part_integral (k : ℕ) (hk : 1 ≤ k) :
    ∫ x in (1 / ((k : ℝ) + 1))..(1 / (k : ℝ)), (1 / x - (k : ℝ)) =
      Real.log ((k : ℝ) + 1) - Real.log (k : ℝ) - 1 / ((k : ℝ) + 1) := by
  have hk_pos : 0 < (k : ℝ) := by exact_mod_cast hk
  have hk1_pos : 0 < (k : ℝ) + 1 := by positivity
  have h_a_pos : 0 < 1 / ((k : ℝ) + 1) := one_div_pos.mpr hk1_pos
  have h_b_pos : 0 < 1 / (k : ℝ) := one_div_pos.mpr hk_pos
  have h_ab_le : 1 / ((k : ℝ) + 1) ≤ 1 / (k : ℝ) := by
    apply one_div_le_one_div_of_le hk_pos
    linarith
  have h_inv_int : (∫ x in (1 / ((k : ℝ) + 1))..(1 / (k : ℝ)), 1 / x) =
      Real.log (1 / (k : ℝ)) - Real.log (1 / ((k : ℝ) + 1)) := by
    rw [integral_one_div_of_pos h_a_pos h_b_pos]
    exact Real.log_div (ne_of_gt h_b_pos) (ne_of_gt h_a_pos)
  have h_cont : ContinuousOn (fun x : ℝ => 1 / x) (Set.Icc (1 / ((k : ℝ) + 1)) (1 / (k : ℝ))) := by
    have : (fun x : ℝ => 1 / x) = Inv.inv := by ext x; exact one_div x
    rw [this]
    apply continuousOn_inv₀.mono
    intro x hx
    have : 0 < x := lt_of_lt_of_le h_a_pos hx.1
    exact ne_of_gt this
  have h_inv_integrable : IntervalIntegrable (fun x => 1 / x) volume (1 / ((k : ℝ) + 1)) (1 / (k : ℝ)) :=
    ContinuousOn.intervalIntegrable_of_Icc h_ab_le h_cont
  have h_int_sub : (∫ x in (1 / ((k : ℝ) + 1))..(1 / (k : ℝ)), (1 / x - (k : ℝ))) =
      (∫ x in (1 / ((k : ℝ) + 1))..(1 / (k : ℝ)), 1 / x) - ∫ x in (1 / ((k : ℝ) + 1))..(1 / (k : ℝ)), (k : ℝ) := by
    apply integral_sub h_inv_integrable (continuous_const.intervalIntegrable _ _)
  have h_log_b : Real.log (1 / (k : ℝ)) = - Real.log (k : ℝ) := by
    rw [one_div, Real.log_inv]
  have h_log_a : Real.log (1 / ((k : ℝ) + 1)) = - Real.log ((k : ℝ) + 1) := by
    rw [one_div, Real.log_inv]
  have h_const_int : (∫ x in (1 / ((k : ℝ) + 1))..(1 / (k : ℝ)), (k : ℝ)) =
      (1 / (k : ℝ) - 1 / ((k : ℝ) + 1)) * (k : ℝ) := by
    rw [intervalIntegral.integral_const, smul_eq_mul]
  have h_alg_const : (1 / (k : ℝ) - 1 / ((k : ℝ) + 1)) * (k : ℝ) = 1 / ((k : ℝ) + 1) := by
    have hk1_ne : (k : ℝ) + 1 ≠ 0 := ne_of_gt hk1_pos
    have hk_ne : (k : ℝ) ≠ 0 := ne_of_gt hk_pos
    field_simp
    ring
  rw [h_int_sub, h_inv_int, h_log_b, h_log_a, h_const_int, h_alg_const]
  ring

/-- 🏆 THEOREM 2: Exact Telescoping Logarithmic Sum Identity -/
theorem telescoping_log_sum (N : ℕ) :
    ∑ k ∈ range N, (Real.log ((k : ℝ) + 2) - Real.log ((k : ℝ) + 1)) =
      Real.log ((N : ℝ) + 1) := by
  have h := sum_range_sub (fun (k : ℕ) => Real.log ((k : ℝ) + 1)) N
  simp only [Nat.cast_zero, zero_add, log_one, sub_zero] at h
  have h_cast : (∑ k ∈ range N, (Real.log ((k : ℝ) + 2) - Real.log ((k : ℝ) + 1))) =
      ∑ k ∈ range N, (Real.log (((k + 1 : ℕ) : ℝ) + 1) - Real.log ((k : ℝ) + 1)) := by
    apply Finset.sum_congr rfl
    intro k _
    push_cast
    ring_nf
  rw [h_cast]
  exact h

/-- 🏆 THEOREM 3: Exact Master Cell-Sum Formula for Fractional Part Integrals -/
theorem fractional_part_cell_sum (N : ℕ) :
    ∑ k ∈ range N, (Real.log ((k : ℝ) + 2) - Real.log ((k : ℝ) + 1) - 1 / ((k : ℝ) + 2)) =
      Real.log ((N : ℝ) + 1) - ∑ k ∈ range N, (1 / ((k : ℝ) + 2)) := by
  rw [sum_sub_distrib]
  have h_tel := telescoping_log_sum N
  rw [h_tel]

end InfoGeometry.Analysis.FractionalPart
