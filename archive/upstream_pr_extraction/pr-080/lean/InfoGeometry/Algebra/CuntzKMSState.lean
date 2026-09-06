import Mathlib.Tactic
import InfoGeometry.Algebra.CuntzTensorQuotient

/-!
# Native finite thermal data for the Cuntz quotient

This owner contains only the finite Boltzmann data used by the Cuntz modular
owners.  It deliberately does not model a commutative diagonal algebra or
claim a positive functional on the whole Cuntz quotient.  The latter requires
the positive extension and completion layer, while the generator KMS equation
is owned by `CuntzGeneratorKMSLogThree`.
-/

noncomputable section

namespace InfoGeometry.Algebra.CuntzKMSState

/-- Boltzmann factor for a finite Cuntz mode. -/
def boltzmannFactor (p : ℕ) (β : ℂ) : ℂ :=
  (p : ℂ) ^ (-β)

/-- Finite mode partition sum. -/
def primonPartition (n : ℕ) (primes : Fin n → ℕ) (β : ℂ) : ℂ :=
  ∑ i : Fin n, boltzmannFactor (primes i) β

/-- Normalized finite-mode weight, when the partition sum is nonzero. -/
def kmsWeight (n : ℕ) (primes : Fin n → ℕ) (β : ℂ) (i : Fin n) : ℂ :=
  boltzmannFactor (primes i) β / primonPartition n primes β

theorem kmsWeight_sum_eq_one
    (n : ℕ) (primes : Fin n → ℕ) (β : ℂ)
    (hZ : primonPartition n primes β ≠ 0) :
    ∑ i : Fin n, kmsWeight n primes β i = 1 := by
  unfold kmsWeight
  rw [← Finset.sum_div]
  exact div_self hZ

theorem kmsWeight_mul_partition
    (n : ℕ) (primes : Fin n → ℕ) (β : ℂ) (i : Fin n)
    (hZ : primonPartition n primes β ≠ 0) :
    kmsWeight n primes β i * primonPartition n primes β =
      boltzmannFactor (primes i) β := by
  unfold kmsWeight
  exact div_mul_cancel₀ _ hZ

end InfoGeometry.Algebra.CuntzKMSState
