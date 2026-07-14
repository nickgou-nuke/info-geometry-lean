import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic
import InfoGeometry.External.Automath.Omega.Folding.Entropy

open Filter
open scoped goldenRatio

namespace Omega.POM

private theorem pom_max_fiber_achievers_hidden_bit_imbalance_ratio_tendsto_inv_golden :
    Tendsto (fun n : ℕ => (Nat.fib n : ℝ) / Nat.fib (n + 1)) atTop
      (nhds (Real.goldenRatio⁻¹)) := by
  have hinv :
      Tendsto (fun n : ℕ => (((Nat.fib (n + 1) : ℝ) / Nat.fib n)⁻¹)) atTop
        (nhds (Real.goldenRatio⁻¹)) := by
    simpa using Omega.Entropy.fib_ratio_tendsto.inv₀ Real.goldenRatio_ne_zero
  refine Tendsto.congr' ?_ hinv
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hfib : (Nat.fib n : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Nat.fib_pos.mpr hn))
  field_simp [hfib]

private theorem pom_max_fiber_achievers_hidden_bit_imbalance_ratio_tendsto_inv_golden_shift :
    Tendsto (fun n : ℕ => (Nat.fib (n + 1) : ℝ) / Nat.fib (n + 2)) atTop
      (nhds (Real.goldenRatio⁻¹)) := by
  have hinv :
      Tendsto (fun n : ℕ => (((Nat.fib (n + 2) : ℝ) / Nat.fib (n + 1))⁻¹)) atTop
        (nhds (Real.goldenRatio⁻¹)) := by
    simpa using Omega.Entropy.fib_ratio_tendsto_golden.inv₀ Real.goldenRatio_ne_zero
  refine Tendsto.congr' ?_ hinv
  filter_upwards [Filter.Eventually.of_forall fun n => Nat.fib_pos.mpr (Nat.succ_pos _)] with n hn
  have hfib : (Nat.fib (n + 1) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hn)
  field_simp [hfib]

private theorem
    pom_max_fiber_achievers_hidden_bit_imbalance_ratio_tendsto_inv_golden_shift_shift :
    Tendsto (fun n : ℕ => (Nat.fib (n + 2) : ℝ) / Nat.fib (n + 3)) atTop
      (nhds (Real.goldenRatio⁻¹)) := by
  simpa [Nat.add_assoc] using
    pom_max_fiber_achievers_hidden_bit_imbalance_ratio_tendsto_inv_golden_shift.comp
      (tendsto_add_atTop_nat 1)

private theorem pom_max_fiber_achievers_hidden_bit_imbalance_ratio_tendsto_inv_golden_cubed :
    Tendsto (fun n : ℕ => (Nat.fib n : ℝ) / Nat.fib (n + 3)) atTop
      (nhds ((Real.goldenRatio⁻¹) ^ 3)) := by
  have hprod0 :
      Tendsto
        (fun n : ℕ =>
          ((Nat.fib n : ℝ) / Nat.fib (n + 1)) *
            ((Nat.fib (n + 1) : ℝ) / Nat.fib (n + 2)) *
              ((Nat.fib (n + 2) : ℝ) / Nat.fib (n + 3)))
        atTop
        (nhds ((Real.goldenRatio⁻¹) * (Real.goldenRatio⁻¹) * (Real.goldenRatio⁻¹))) := by
    simpa [mul_assoc] using
      pom_max_fiber_achievers_hidden_bit_imbalance_ratio_tendsto_inv_golden.mul
        (pom_max_fiber_achievers_hidden_bit_imbalance_ratio_tendsto_inv_golden_shift.mul
          pom_max_fiber_achievers_hidden_bit_imbalance_ratio_tendsto_inv_golden_shift_shift)
  have hprod :
      Tendsto
        (fun n : ℕ =>
          ((Nat.fib n : ℝ) / Nat.fib (n + 1)) *
            ((Nat.fib (n + 1) : ℝ) / Nat.fib (n + 2)) *
              ((Nat.fib (n + 2) : ℝ) / Nat.fib (n + 3)))
        atTop
        (nhds ((Real.goldenRatio⁻¹) ^ 3)) := by
    simpa [pow_succ, mul_assoc] using hprod0
  refine Tendsto.congr' ?_ hprod
  filter_upwards [Filter.Eventually.of_forall fun _ => True.intro] with n _
  have hfib1 : (Nat.fib (n + 1) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Nat.fib_pos.mpr (Nat.succ_pos n)))
  have hfib2 : (Nat.fib (n + 2) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Nat.fib_pos.mpr (Nat.succ_pos (n + 1))))
  field_simp [hfib1, hfib2]

/-- Paper label: `cor:pom-max-fiber-achievers-hidden-bit-imbalance`. The parity-split
max-achiever formulas reduce the even and odd hidden-bit imbalances to the same normalized
Fibonacci ratio `F_k / F_{k+3}`, whose limit is the universal constant `φ^{-3}`. -/
theorem paper_pom_max_fiber_achievers_hidden_bit_imbalance :
    (∀ k : ℕ,
      |((Nat.fib (k + 2) : ℝ) / Nat.fib (k + 3) -
          (Nat.fib (k + 1) : ℝ) / Nat.fib (k + 3))| =
        (Nat.fib k : ℝ) / Nat.fib (k + 3)) ∧
      (∀ k : ℕ,
        |(((1 / 2 : ℝ) + (Nat.fib k : ℝ) / (2 * Nat.fib (k + 3) : ℝ)) -
            ((1 / 2 : ℝ) - (Nat.fib k : ℝ) / (2 * Nat.fib (k + 3) : ℝ)))| =
          (Nat.fib k : ℝ) / Nat.fib (k + 3)) ∧
      Tendsto (fun k : ℕ => (Nat.fib k : ℝ) / Nat.fib (k + 3)) atTop
        (nhds ((Real.goldenRatio⁻¹ : ℝ) ^ 3)) := by
  refine ⟨?_, ?_, pom_max_fiber_achievers_hidden_bit_imbalance_ratio_tendsto_inv_golden_cubed⟩
  · intro k
    have hden_pos : 0 < (Nat.fib (k + 3) : ℝ) := by
      exact_mod_cast Nat.fib_pos.mpr (by omega : 0 < k + 3)
    have hden_ne : (Nat.fib (k + 3) : ℝ) ≠ 0 := ne_of_gt hden_pos
    have hfib : (Nat.fib (k + 2) : ℝ) = Nat.fib (k + 1) + Nat.fib k := by
      simpa [add_comm] using
        (show (Nat.fib (k + 2) : ℝ) = Nat.fib k + Nat.fib (k + 1) by
          exact_mod_cast Nat.fib_add_two (n := k))
    have hnonneg :
        0 ≤ (Nat.fib (k + 2) : ℝ) / Nat.fib (k + 3) -
          (Nat.fib (k + 1) : ℝ) / Nat.fib (k + 3) := by
      rw [sub_nonneg]
      exact div_le_div_of_nonneg_right (by nlinarith [hfib]) hden_pos.le
    rw [abs_of_nonneg hnonneg]
    field_simp [hden_ne]
    nlinarith [hfib]
  · intro k
    have hnonneg :
        0 ≤
          (((1 / 2 : ℝ) + (Nat.fib k : ℝ) / (2 * Nat.fib (k + 3) : ℝ)) -
            ((1 / 2 : ℝ) - (Nat.fib k : ℝ) / (2 * Nat.fib (k + 3) : ℝ))) := by
      have hdelta_nonneg : 0 ≤ (Nat.fib k : ℝ) / (2 * Nat.fib (k + 3) : ℝ) := by
        positivity
      linarith
    rw [abs_of_nonneg hnonneg]
    ring_nf

end Omega.POM
