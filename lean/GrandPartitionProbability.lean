import GrandPartitionRational
import Mathlib

noncomputable section

open Polynomial Finset
open scoped BigOperators

section ProbabilityLayer

/-- Unnormalized occupancy-sector weight. -/
def occupancyWeight
    (n : ℕ) (q : ℝ) (b : ℕ → ℝ) (m : ℕ) : ℝ :=
  q ^ m * canonicalPartition b n m

/-- Finite occupancy PMF obtained from the grand partition function. -/
def occupancyPMF
    (n : ℕ) (q : ℝ) (b : ℕ → ℝ) (m : ℕ) : ℝ :=
  occupancyWeight n q b m / grandPartition n q b

/-- Single-site Bernoulli responsibility. -/
def siteResponsibility (q bi : ℝ) : ℝ :=
  q * bi / (1 + q * bi)

theorem canonicalPartition_nonneg
    (b : ℕ → ℝ) (hb : ∀ i, 0 ≤ b i) :
    ∀ n m, 0 ≤ canonicalPartition b n m := by
  intro n
  induction n with
  | zero =>
      intro m
      cases m with
      | zero => simp [canonical_zero_zero]
      | succ m =>
          rw [canonical_degree_bound (b := b) 0 (m + 1) (Nat.succ_pos m)]
  | succ n ih =>
      intro m
      cases m with
      | zero =>
          rw [canonical_succ_zero]
          exact ih 0
      | succ m =>
          rw [canonical_succ_succ]
          exact add_nonneg (ih (m + 1)) (mul_nonneg (hb n) (ih m))

theorem grandPartition_pos
    (n : ℕ) (q : ℝ) (b : ℕ → ℝ)
    (hq : 0 ≤ q) (hb : ∀ i, 0 ≤ b i) :
    0 < grandPartition n q b := by
  rw [grandPartition_eq_product]
  apply Finset.prod_pos
  intro i hi
  exact add_pos_of_pos_of_nonneg zero_lt_one (mul_nonneg hq (hb i))

theorem occupancyWeight_nonneg
    (n : ℕ) (q : ℝ) (b : ℕ → ℝ)
    (hq : 0 ≤ q) (hb : ∀ i, 0 ≤ b i) (m : ℕ) :
    0 ≤ occupancyWeight n q b m := by
  exact mul_nonneg (pow_nonneg hq m) (canonicalPartition_nonneg b hb n m)

theorem occupancyWeight_sum
    (n : ℕ) (q : ℝ) (b : ℕ → ℝ) :
    ∑ m ∈ range (n + 1), occupancyWeight n q b m =
      grandPartition n q b := by
  rw [grandPartition_eq_sum]
  rfl

theorem occupancyPMF_nonneg
    (n : ℕ) (q : ℝ) (b : ℕ → ℝ)
    (hq : 0 ≤ q) (hb : ∀ i, 0 ≤ b i) (m : ℕ) :
    0 ≤ occupancyPMF n q b m := by
  exact div_nonneg
    (occupancyWeight_nonneg n q b hq hb m)
    (grandPartition_pos n q b hq hb).le

theorem occupancyPMF_sum_one
    (n : ℕ) (q : ℝ) (b : ℕ → ℝ)
    (hΞ : grandPartition n q b ≠ 0) :
    ∑ m ∈ range (n + 1), occupancyPMF n q b m = 1 := by
  rw [occupancyPMF, ← Finset.sum_div, occupancyWeight_sum]
  exact div_self hΞ

/-- PMF first raw moment. -/
def pmfMean
    (n : ℕ) (q : ℝ) (b : ℕ → ℝ) : ℝ :=
  ∑ m ∈ range (n + 1), (m : ℝ) * occupancyPMF n q b m

/-- PMF second raw moment. -/
def pmfSecondRaw
    (n : ℕ) (q : ℝ) (b : ℕ → ℝ) : ℝ :=
  ∑ m ∈ range (n + 1), (m : ℝ) ^ 2 * occupancyPMF n q b m

/-- PMF variance. -/
def pmfVariance
    (n : ℕ) (q : ℝ) (b : ℕ → ℝ) : ℝ :=
  pmfSecondRaw n q b - pmfMean n q b ^ 2

theorem pmfMean_eq_expectedOccupancy
    (n : ℕ) (q : ℝ) (b : ℕ → ℝ)
    (hΞ : grandPartition n q b ≠ 0) :
    pmfMean n q b = expectedOccupancy n q b := by
  unfold pmfMean occupancyPMF occupancyWeight expectedOccupancy
  field_simp [hΞ]
  rw [eval_euler_grandPartitionPoly_eq_sum]
  apply Finset.sum_congr rfl
  intro m hm
  ring

theorem pmfSecondRaw_eq_secondRawOccupancy
    (n : ℕ) (q : ℝ) (b : ℕ → ℝ)
    (hΞ : grandPartition n q b ≠ 0) :
    pmfSecondRaw n q b = secondRawOccupancy n q b := by
  unfold pmfSecondRaw occupancyPMF occupancyWeight secondRawOccupancy
  field_simp [hΞ]
  rw [eval_eulerOp_euler_grandPartitionPoly_eq_sum]
  apply Finset.sum_congr rfl
  intro m hm
  ring

theorem pmfVariance_eq_varianceOccupancy
    (n : ℕ) (q : ℝ) (b : ℕ → ℝ)
    (hΞ : grandPartition n q b ≠ 0) :
    pmfVariance n q b = varianceOccupancy n q b := by
  rw [pmfVariance, varianceOccupancy,
    pmfMean_eq_expectedOccupancy n q b hΞ,
    pmfSecondRaw_eq_secondRawOccupancy n q b hΞ]

theorem siteResponsibility_nonneg
    {q bi : ℝ} (hq : 0 ≤ q) (hbi : 0 ≤ bi) :
    0 ≤ siteResponsibility q bi := by
  have hden : 0 < 1 + q * bi :=
    add_pos_of_pos_of_nonneg zero_lt_one (mul_nonneg hq hbi)
  exact div_nonneg (mul_nonneg hq hbi) hden.le

theorem siteResponsibility_le_one
    {q bi : ℝ} (hq : 0 ≤ q) (hbi : 0 ≤ bi) :
    siteResponsibility q bi ≤ 1 := by
  have hden : 0 < 1 + q * bi :=
    add_pos_of_pos_of_nonneg zero_lt_one (mul_nonneg hq hbi)
  rw [siteResponsibility, div_le_one hden]
  linarith

end ProbabilityLayer
