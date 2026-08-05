import GrandPartitionTransform
import Mathlib.Algebra.Polynomial.Derivative

noncomputable section

open Polynomial Finset
open scoped BigOperators

section EulerLayer

variable {R : Type*} [CommRing R]

/-- Algebraic Euler operator `𝒟P = X P'`. -/
def eulerOp (P : R[X]) : R[X] :=
  X * derivative P

@[simp]
theorem eulerOp_coeff_zero (P : R[X]) :
    (eulerOp P).coeff 0 = 0 := by
  simp [eulerOp]

@[simp]
theorem eulerOp_coeff_succ (P : R[X]) (m : ℕ) :
    (eulerOp P).coeff (m + 1) =
      (m + 1 : R) * P.coeff (m + 1) := by
  rw [eulerOp, coeff_X_mul, coeff_derivative, mul_comm]

/-- The Euler operator diagonalizes the monomial coefficient sectors. -/
theorem eulerOp_coeff (P : R[X]) (m : ℕ) :
    (eulerOp P).coeff m = (m : R) * P.coeff m := by
  cases m with
  | zero => simp
  | succ m => simpa [Nat.cast_succ] using eulerOp_coeff_succ P m

/-- Evaluation commutes with the Euler construction in the expected algebraic
form `eval q (𝒟P) = q * eval q P'`. -/
theorem eval_eulerOp (P : R[X]) (q : R) :
    (eulerOp P).eval q = q * (derivative P).eval q := by
  simp [eulerOp]

/-- Finite monomial expansion of the first occupancy-moment polynomial. -/
theorem euler_grandPartitionPoly_as_sum
    (b : ℕ → R) (n : ℕ) :
    eulerOp (grandPartitionPoly b n) =
      ∑ m ∈ range (n + 1),
        monomial m ((m : R) * canonicalPartition b n m) := by
  ext k
  rw [eulerOp_coeff, Polynomial.finset_sum_coeff]
  by_cases hk : k ∈ range (n + 1)
  · rw [Finset.sum_eq_single k]
    · simp [canonicalPartition]
    · intro j hj hne
      rw [Polynomial.coeff_monomial]
      simp [hne, Ne.symm hne]
    · intro hknot
      exact (hknot hk).elim
  · have hnot : ¬ k < n + 1 := by
      simpa [Finset.mem_range] using hk
    have hnk : n < k :=
      Nat.lt_of_lt_of_le (Nat.lt_succ_self n) (Nat.not_lt.mp hnot)
    have hzero : (grandPartitionPoly b n).coeff k = 0 := by
      change canonicalPartition b n k = 0
      exact canonical_degree_bound (b := b) n k hnk
    rw [hzero, mul_zero]
    symm
    apply Finset.sum_eq_zero
    intro j hj
    rw [Polynomial.coeff_monomial]
    have hkj : k ≠ j := by
      intro h
      subst j
      exact hk hj
    simp [hkj, Ne.symm hkj]

/-- Finite monomial expansion of the second raw occupancy-moment polynomial. -/
theorem eulerOp_euler_grandPartitionPoly_as_sum
    (b : ℕ → R) (n : ℕ) :
    eulerOp (eulerOp (grandPartitionPoly b n)) =
      ∑ m ∈ range (n + 1),
        monomial m ((m : R) ^ 2 * canonicalPartition b n m) := by
  ext k
  rw [eulerOp_coeff, eulerOp_coeff, Polynomial.finset_sum_coeff]
  by_cases hk : k ∈ range (n + 1)
  · rw [Finset.sum_eq_single k]
    · simp [canonicalPartition]
      ring
    · intro j hj hne
      rw [Polynomial.coeff_monomial]
      simp [hne, Ne.symm hne]
    · intro hknot
      exact (hknot hk).elim
  · have hnot : ¬ k < n + 1 := by
      simpa [Finset.mem_range] using hk
    have hnk : n < k :=
      Nat.lt_of_lt_of_le (Nat.lt_succ_self n) (Nat.not_lt.mp hnot)
    have hzero : (grandPartitionPoly b n).coeff k = 0 := by
      change canonicalPartition b n k = 0
      exact canonical_degree_bound (b := b) n k hnk
    rw [hzero, mul_zero, mul_zero]
    symm
    apply Finset.sum_eq_zero
    intro j hj
    rw [Polynomial.coeff_monomial]
    have hkj : k ≠ j := by
      intro h
      subst j
      exact hk hj
    simp [hkj, Ne.symm hkj]

/-- The evaluated Euler polynomial is the unnormalized first occupancy
moment. -/
theorem eval_euler_grandPartitionPoly_eq_sum
    (b : ℕ → R) (n : ℕ) (q : R) :
    (eulerOp (grandPartitionPoly b n)).eval q =
      ∑ m ∈ range (n + 1),
        (m : R) * q ^ m * canonicalPartition b n m := by
  rw [euler_grandPartitionPoly_as_sum, eval_finset_sum]
  apply Finset.sum_congr rfl
  intro m hm
  rw [eval_monomial]
  ring

/-- Applying the Euler operator twice produces the unnormalized second raw
occupancy moment. -/
theorem eval_eulerOp_euler_grandPartitionPoly_eq_sum
    (b : ℕ → R) (n : ℕ) (q : R) :
    (eulerOp (eulerOp (grandPartitionPoly b n))).eval q =
      ∑ m ∈ range (n + 1),
        (m : R) ^ 2 * q ^ m * canonicalPartition b n m := by
  rw [eulerOp_euler_grandPartitionPoly_as_sum, eval_finset_sum]
  apply Finset.sum_congr rfl
  intro m hm
  rw [eval_monomial]
  ring

end EulerLayer
