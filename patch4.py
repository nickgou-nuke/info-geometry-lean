import re

with open('lean/Omega/POM/MaxFiberAchieversHiddenBitProbSpectrum.lean', 'r') as f:
    content = f.read()

old_1 = """private theorem pom_max_fiber_achievers_hidden_bit_prob_spectrum_ratio_tendsto_inv_golden_shift :
    Tendsto (fun n : ℕ => (Nat.fib (n + 1) : ℝ) / Nat.fib (n + 2)) atTop
      (nhds (Real.goldenRatio⁻¹)) := by
  have h := tendsto_fib_div_fib_succ_atTop.comp (tendsto_add_atTop_nat (1 : ℕ))
  rw [Real.inv_goldenRatio]
  simpa [Nat.add_assoc] using h"""

new_1 = """private theorem pom_max_fiber_achievers_hidden_bit_prob_spectrum_ratio_tendsto_inv_golden_shift :
    Tendsto (fun n : ℕ => (Nat.fib (n + 1) : ℝ) / Nat.fib (n + 2)) atTop
      (nhds (Real.goldenRatio⁻¹)) := by
  have h := tendsto_fib_div_fib_succ_atTop.comp (tendsto_add_atTop_nat (1 : ℕ))
  rw [Real.inv_goldenRatio]
  have heq : (fun n : ℕ => (Nat.fib (n + 1) : ℝ) / Nat.fib (n + 2)) =
      ((fun n => (Nat.fib n : ℝ) / Nat.fib (n + 1)) ∘ fun a => a + 1) := by
    funext n
    simp only [Function.comp_apply]
    congr 2
    omega
  rw [heq]
  exact h"""

old_2 = """private theorem pom_max_fiber_achievers_hidden_bit_prob_spectrum_ratio_tendsto_inv_golden_shift2 :
    Tendsto (fun n : ℕ => (Nat.fib (n + 2) : ℝ) / Nat.fib (n + 3)) atTop
      (nhds (Real.goldenRatio⁻¹)) := by
  simpa [Nat.add_assoc] using
    pom_max_fiber_achievers_hidden_bit_prob_spectrum_ratio_tendsto_inv_golden_shift.comp
      (tendsto_add_atTop_nat (1 : ℕ))"""

new_2 = """private theorem pom_max_fiber_achievers_hidden_bit_prob_spectrum_ratio_tendsto_inv_golden_shift2 :
    Tendsto (fun n : ℕ => (Nat.fib (n + 2) : ℝ) / Nat.fib (n + 3)) atTop
      (nhds (Real.goldenRatio⁻¹)) := by
  have h := pom_max_fiber_achievers_hidden_bit_prob_spectrum_ratio_tendsto_inv_golden_shift.comp (tendsto_add_atTop_nat (1 : ℕ))
  have heq : (fun n : ℕ => (Nat.fib (n + 2) : ℝ) / Nat.fib (n + 3)) =
      ((fun n => (Nat.fib (n + 1) : ℝ) / Nat.fib (n + 2)) ∘ fun a => a + 1) := by
    funext n
    simp only [Function.comp_apply]
    congr 2 <;> omega
  rw [heq]
  exact h"""

if old_1 in content:
    content = content.replace(old_1, new_1)
    print("Patched 1")
else:
    print("Failed to patch 1")

if old_2 in content:
    content = content.replace(old_2, new_2)
    print("Patched 2")
else:
    print("Failed to patch 2")

with open('lean/Omega/POM/MaxFiberAchieversHiddenBitProbSpectrum.lean', 'w') as f:
    f.write(content)
