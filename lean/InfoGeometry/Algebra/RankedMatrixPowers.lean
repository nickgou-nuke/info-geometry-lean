import Mathlib

/-!
# Matrix powers with strictly rank-decreasing support

A support theorem over arbitrary semirings. No positivity, absence of zero
divisors, stochastic normalization, or minimal-nilpotence-index claim is needed.
-/

namespace InfoGeometry.Algebra.RankedMatrixPowers

variable {ι R : Type*} [Fintype ι] [DecidableEq ι] [Semiring R]

/-- A path of length k needs at least k units of natural-valued rank drop. -/
theorem pow_entry_eq_zero_of_rank_lt
    (K : Matrix ι ι R) (rank : ι → ℕ)
    (hK : ∀ i j, K i j ≠ 0 → rank j < rank i) (k : ℕ) :
    ∀ i j, rank i < rank j + k → (K ^ k) i j = 0 := by
  induction k with
  | zero =>
      intro i j hij
      have hne : i ≠ j := by
        intro heq
        subst j
        omega
      simp [Matrix.one_apply, hne]
  | succ k ih =>
      intro i j hij
      rw [pow_succ', Matrix.mul_apply]
      apply Finset.sum_eq_zero
      intro v _
      by_cases hz : K i v = 0
      · rw [hz, zero_mul]
      · have hdrop := hK i v hz
        have hremaining : rank v < rank j + k := by omega
        rw [ih v j hremaining, mul_zero]

/-- Nonzero power entries certify the corresponding rank budget. -/
theorem rank_add_le_of_pow_entry_ne_zero
    (K : Matrix ι ι R) (rank : ι → ℕ)
    (hK : ∀ i j, K i j ≠ 0 → rank j < rank i)
    (k : ℕ) {i j : ι} (h : (K ^ k) i j ≠ 0) :
    rank j + k ≤ rank i := by
  by_contra hnot
  exact h (pow_entry_eq_zero_of_rank_lt K rank hK k i j (by omega))

/-- A strict upper bound on all ranks is a nilpotence exponent. -/
theorem pow_eq_zero_of_rank_bound
    (K : Matrix ι ι R) (rank : ι → ℕ)
    (hK : ∀ i j, K i j ≠ 0 → rank j < rank i)
    (N : ℕ) (hN : ∀ i, rank i < N) : K ^ N = 0 := by
  ext i j
  apply pow_entry_eq_zero_of_rank_lt K rank hK N i j
  have hi := hN i
  omega

/-- A total computable bound; the empty-index convention is one. -/
def rankHorizon (rank : ι → ℕ) : ℕ := Finset.univ.sup rank + 1

theorem rank_lt_rankHorizon (rank : ι → ℕ) (i : ι) :
    rank i < rankHorizon rank := by
  have h : rank i ≤ Finset.univ.sup rank := Finset.le_sup (Finset.mem_univ i)
  exact Nat.lt_succ_of_le h

theorem pow_rankHorizon_eq_zero
    (K : Matrix ι ι R) (rank : ι → ℕ)
    (hK : ∀ i j, K i j ≠ 0 → rank j < rank i) :
    K ^ rankHorizon rank = 0 :=
  pow_eq_zero_of_rank_bound K rank hK _ (rank_lt_rankHorizon rank)

end InfoGeometry.Algebra.RankedMatrixPowers
