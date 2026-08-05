import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

open Polynomial Finset

section CommutativeAlgebra

variable {R : Type*} [CommRing R]
variable (b : ℕ → R)

/-- The recursive ordinary generating polynomial -/
def grandPartitionPoly : ℕ → R[X]
  | 0 => 1
  | n + 1 => grandPartitionPoly n * (1 + C (b n) * X)

/-- Canonical partition coefficients extracted via algebraic degree -/
def canonicalPartition (n m : ℕ) : R :=
  (grandPartitionPoly b n).coeff m

-- 1. Base Case Zero
lemma canonical_zero_zero :
    canonicalPartition b 0 0 = 1 := by
  simp [canonicalPartition, grandPartitionPoly]

-- 2. Successor Base Case
lemma canonical_succ_zero (n : ℕ) :
    canonicalPartition b (n + 1) 0 = canonicalPartition b n 0 := by
  simp [canonicalPartition, grandPartitionPoly, mul_add, mul_assoc]

-- 3. The Core DP Recurrence
lemma canonical_succ_succ (n m : ℕ) :
    canonicalPartition b (n + 1) (m + 1) =
      canonicalPartition b n (m + 1) + b n * canonicalPartition b n m := by
  simp [canonicalPartition, grandPartitionPoly, mul_add, mul_assoc, mul_comm]

-- 4. Finite Support Bound
lemma canonical_degree_bound (n m : ℕ) (h : n < m) :
    canonicalPartition b n m = 0 := by
  induction n generalizing m with
  | zero =>
      have hm : m ≠ 0 := Nat.ne_of_gt h
      simp [canonicalPartition, grandPartitionPoly, hm]
  | succ n ih =>
      cases m with
      | zero =>
          exact (Nat.not_lt_zero _ h).elim
      | succ m =>
          have hnm : n < m := Nat.succ_lt_succ_iff.mp h
          rw [canonical_succ_succ (b := b) n m]
          rw [ih (m + 1) (Nat.lt_succ_of_lt hnm), ih m hnm]
          simp

-- 5. Product Characterization
lemma grandPartitionPoly_eq_prod (n : ℕ) :
    grandPartitionPoly b n = ∏ i ∈ range n, (1 + C (b i) * X) := by
  induction n with
  | zero =>
      simp [grandPartitionPoly]
  | succ n ih =>
      simp [grandPartitionPoly, ih, Finset.prod_range_succ]

-- 6. Finite Sum Expansion (The core evaluation prep)
lemma grandPartitionPoly_as_sum (n : ℕ) :
    grandPartitionPoly b n =
      ∑ m ∈ range (n + 1), C (canonicalPartition b n m) * X ^ m := by
  ext k
  by_cases hk : k ∈ range (n + 1)
  · simp [canonicalPartition, Polynomial.coeff_C_mul_X_pow, hk]
  · have hnot : ¬ k < n + 1 := by
      simpa [Finset.mem_range] using hk
    have hnk : n < k :=
      Nat.lt_of_lt_of_le (Nat.lt_succ_self n) (Nat.not_lt.mp hnot)
    simp [canonicalPartition, Polynomial.coeff_C_mul_X_pow, hk,
      canonical_degree_bound (b := b) n k hnk]

end CommutativeAlgebra
