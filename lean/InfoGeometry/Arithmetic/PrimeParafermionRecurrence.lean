import InfoGeometry.Arithmetic.PrimeParafermionGrandCanonicalClock
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Finite prime parafermion recurrence

Recurrent algebraic laws for the canonical complex finite parafermion factor.
These are finite `Finset.range` identities; no limiting or convergence claim is
made.
-/

namespace InfoGeometry.Arithmetic.PrimeParafermionGrandCanonicalClock

/-- Increasing the occupancy cutoff adds exactly the next monomial. -/
theorem finiteParafermionLocalFactor_succ (κ : ℕ) (x : ℂ) :
    finiteParafermionLocalFactor (κ + 1) x =
      finiteParafermionLocalFactor κ x + x ^ κ := by
  simp [finiteParafermionLocalFactor, Finset.sum_range_succ]

/-- Denominator-cleared finite geometric identity, valid without `x ≠ 1`. -/
theorem finiteParafermionLocalFactor_mul_one_sub (κ : ℕ) (x : ℂ) :
    finiteParafermionLocalFactor κ x * (1 - x) = 1 - x ^ κ := by
  simpa [finiteParafermionLocalFactor, mul_comm, mul_left_comm, mul_assoc] using
    geom_sum_mul_neg x κ

/-- Adding a new prime mode multiplies the finite partition by its local factor. -/
theorem finiteGrandParafermionPartition_insert
    (S : Finset Nat.Primes) (p : Nat.Primes) (hp : p ∉ S)
    (z s : ℂ) (κ : ℕ) :
    finiteGrandParafermionPartition (insert p S) z s κ =
      finiteParafermionLocalFactor κ (grandComplexPrimeWeight z s p) *
        finiteGrandParafermionPartition S z s κ := by
  simp [finiteGrandParafermionPartition, hp]

/-- Global denominator-cleared identity for a finite prime cutoff. -/
theorem finiteGrandParafermionPartition_mul_denominator
    (S : Finset Nat.Primes) (z s : ℂ) (κ : ℕ) :
    finiteGrandParafermionPartition S z s κ *
        (∏ p ∈ S, (1 - grandComplexPrimeWeight z s p)) =
      ∏ p ∈ S, (1 - grandComplexPrimeWeight z s p ^ κ) := by
  unfold finiteGrandParafermionPartition
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun p _hp =>
    finiteParafermionLocalFactor_mul_one_sub κ (grandComplexPrimeWeight z s p)

end InfoGeometry.Arithmetic.PrimeParafermionGrandCanonicalClock
