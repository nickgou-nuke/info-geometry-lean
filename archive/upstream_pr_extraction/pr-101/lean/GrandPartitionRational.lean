import GrandPartitionEuler

noncomputable section

open Polynomial Finset
open scoped BigOperators

section RationalLayer

variable {K : Type*} [Field K]

/-- First raw occupancy moment normalized by the grand partition function. -/
def expectedOccupancy
    (n : ℕ) (q : K) (b : ℕ → K) : K :=
  (eulerOp (grandPartitionPoly b n)).eval q / grandPartition n q b

/-- Second raw occupancy moment normalized by the grand partition function. -/
def secondRawOccupancy
    (n : ℕ) (q : K) (b : ℕ → K) : K :=
  (eulerOp (eulerOp (grandPartitionPoly b n))).eval q /
    grandPartition n q b

/-- Algebraic variance obtained from the first two raw moments. -/
def varianceOccupancy
    (n : ℕ) (q : K) (b : ℕ → K) : K :=
  secondRawOccupancy n q b - expectedOccupancy n q b ^ 2

theorem expectedOccupancy_mul_partition
    (n : ℕ) (q : K) (b : ℕ → K)
    (hΞ : grandPartition n q b ≠ 0) :
    expectedOccupancy n q b * grandPartition n q b =
      (eulerOp (grandPartitionPoly b n)).eval q := by
  simp [expectedOccupancy, hΞ]

theorem secondRawOccupancy_mul_partition
    (n : ℕ) (q : K) (b : ℕ → K)
    (hΞ : grandPartition n q b ≠ 0) :
    secondRawOccupancy n q b * grandPartition n q b =
      (eulerOp (eulerOp (grandPartitionPoly b n))).eval q := by
  simp [secondRawOccupancy, hΞ]

/-- Field-level prior/activity conversion. -/
theorem prior_normalization
    (n : ℕ) (α : K) (b : ℕ → K)
    (hα : 1 - α ≠ 0) :
    (∏ i ∈ range n, ((1 - α) + α * b i)) =
      (1 - α) ^ n * grandPartition n (α / (1 - α)) b := by
  apply prior_normalization_of_relation
  field_simp [hα]

end RationalLayer
