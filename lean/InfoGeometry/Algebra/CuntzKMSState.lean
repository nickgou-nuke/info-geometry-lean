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

theorem primonPartition_eq_sum (n : ℕ) (primes : Fin n → ℕ) (β : ℂ) :
    primonPartition n primes β =
      ∑ i : Fin n, (primes i : ℂ) ^ (-β) := by
  rfl

theorem kmsWeight_eq_boltzmann_div_partition
    (n : ℕ) (primes : Fin n → ℕ) (β : ℂ) (i : Fin n) :
    kmsWeight n primes β i =
      (primes i : ℂ) ^ (-β) / primonPartition n primes β := by
  rfl

end InfoGeometry.Algebra.CuntzKMSState
