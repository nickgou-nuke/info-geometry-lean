import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.PowerVarianceCumulants

namespace InfoGeometry.Canonical

open scoped BigOperators

noncomputable def cumulantCoefficient (ν : ℝ) (n : ℕ) : ℝ :=
  ∏ m ∈ Finset.Icc 2 (n - 1), ((m : ℝ) - ((m : ℝ) - 1) * ν)

noncomputable def powerVarianceCumulant (ν μ : ℝ) (n : ℕ) : ℝ :=
  cumulantCoefficient ν n * (μ ^ ((n : ℝ) - ((n : ℝ) - 1) * ν))

theorem cumulantCoefficient_at_two (n : ℕ) (h : 3 ≤ n) : cumulantCoefficient 2 n = 0 := by
  dsimp [cumulantCoefficient]
  have h_mem : 2 ∈ Finset.Icc 2 (n - 1) := by
    rw [Finset.mem_Icc]
    omega
  have h_eq : ((2 : ℝ) - ((2 : ℝ) - 1) * 2) = 0 := by norm_num
  exact Finset.prod_eq_zero h_mem h_eq

theorem cumulantCoefficient_at_one (n : ℕ) : cumulantCoefficient 1 n = 1 := by
  dsimp [cumulantCoefficient]
  apply Finset.prod_eq_one
  intro m _
  ring

lemma prod_Icc_two_eq_factorial (k : ℕ) : ∏ m ∈ Finset.Icc 2 k, (m : ℝ) = (Nat.factorial k : ℝ) := by
  induction k with
  | zero =>
    have h : Finset.Icc 2 0 = ∅ := Finset.Icc_eq_empty (by omega)
    rw [h, Finset.prod_empty, Nat.factorial_zero, Nat.cast_one]
  | succ k ih =>
    by_cases hk : k = 0
    · rw [hk]
      have h : Finset.Icc 2 1 = ∅ := Finset.Icc_eq_empty (by omega)
      rw [h, Finset.prod_empty, Nat.factorial_one, Nat.cast_one]
    · have h_pos : 2 ≤ k + 1 := by omega
      rw [Finset.prod_Icc_succ_top h_pos, ih, Nat.factorial_succ, Nat.cast_mul]
      ring

theorem cumulantCoefficient_at_zero (n : ℕ) : cumulantCoefficient 0 n = (Nat.factorial (n - 1) : ℝ) := by
  dsimp [cumulantCoefficient]
  have H : (∏ m ∈ Finset.Icc 2 (n - 1), ((m : ℝ) - ((m : ℝ) - 1) * 0)) = ∏ m ∈ Finset.Icc 2 (n - 1), (m : ℝ) := by
    apply Finset.prod_congr rfl
    intro x _
    ring
  rw [H]
  exact prod_Icc_two_eq_factorial (n - 1)

theorem powerVarianceCumulant_at_two (μ : ℝ) (n : ℕ) (h : 3 ≤ n) :
    powerVarianceCumulant 2 μ n = 0 := by
  dsimp [powerVarianceCumulant]
  rw [cumulantCoefficient_at_two n h, zero_mul]

theorem powerVarianceCumulant_at_one (μ : ℝ) (n : ℕ) :
    powerVarianceCumulant 1 μ n = μ := by
  dsimp [powerVarianceCumulant]
  rw [cumulantCoefficient_at_one n]
  have H : (n : ℝ) - ((n : ℝ) - 1) * 1 = 1 := by ring
  rw [H, Real.rpow_one, one_mul]

theorem powerVarianceCumulant_at_zero (μ : ℝ) (n : ℕ) :
    powerVarianceCumulant 0 μ n = (Nat.factorial (n - 1) : ℝ) * (μ ^ n) := by
  dsimp [powerVarianceCumulant]
  rw [cumulantCoefficient_at_zero n]
  have H : (n : ℝ) - ((n : ℝ) - 1) * 0 = (n : ℝ) := by ring
  rw [H, Real.rpow_natCast]

end InfoGeometry.Canonical
