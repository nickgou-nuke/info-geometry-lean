import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Bosonic Primon Partition Function

Finite Euler-product layer for the bosonic Primon gas.

For each prime mode `p`, a bosonic occupation number `k : ℕ` is allowed with
no exclusion cutoff except the finite truncation `K` used here.  Its Boltzmann
weight is `(p ^ (-β)) ^ k`.

The key finite theorem is the algebraic core of the Euler product:

`(Σ_k a^k) * (Σ_l b^l) = Σ_{k,l} a^k b^l`.

For `a = p^(-β)` and `b = q^(-β)`, this is the finite two-prime truncation of
the bosonic partition function whose infinite prime/mode limit is the usual
zeta Euler product in the analytic regime.
-/

noncomputable section

def primeBoltzmannWeight (p : ℕ) (β : ℝ) : ℝ :=
  (p : ℝ) ^ (-β)

def bosonOccupationWeight (p : ℕ) (β : ℝ) (k : ℕ) : ℝ :=
  (primeBoltzmannWeight p β) ^ k

def singlePrimeBosonPartition (p : ℕ) (β : ℝ) (K : ℕ) : ℝ :=
  (Finset.range (K + 1)).sum fun k => bosonOccupationWeight p β k

def twoPrimeBosonPartition (p q : ℕ) (β : ℝ) (K : ℕ) : ℝ :=
  (Finset.range (K + 1)).sum fun k =>
    (Finset.range (K + 1)).sum fun l =>
      bosonOccupationWeight p β k * bosonOccupationWeight q β l

theorem bosonOccupationWeight_zero (p : ℕ) (β : ℝ) :
    bosonOccupationWeight p β 0 = 1 := by
  simp [bosonOccupationWeight]

theorem bosonOccupationWeight_succ (p : ℕ) (β : ℝ) (k : ℕ) :
    bosonOccupationWeight p β (k + 1) =
      bosonOccupationWeight p β k * primeBoltzmannWeight p β := by
  simp [bosonOccupationWeight, pow_succ]

theorem singlePrimeBosonPartition_succ (p : ℕ) (β : ℝ) (K : ℕ) :
    singlePrimeBosonPartition p β (K + 1) =
      singlePrimeBosonPartition p β K + bosonOccupationWeight p β (K + 1) := by
  simp [singlePrimeBosonPartition, Finset.sum_range_succ]

theorem finite_two_prime_euler_product (p q : ℕ) (β : ℝ) (K : ℕ) :
    singlePrimeBosonPartition p β K * singlePrimeBosonPartition q β K =
      twoPrimeBosonPartition p q β K := by
  simp [singlePrimeBosonPartition, twoPrimeBosonPartition, Finset.sum_mul_sum]

/-- Concrete finite statement for the first two prime modes `2` and `3`. -/
theorem finite_2_3_bosonic_partition (β : ℝ) (K : ℕ) :
    singlePrimeBosonPartition 2 β K * singlePrimeBosonPartition 3 β K =
      twoPrimeBosonPartition 2 3 β K :=
  finite_two_prime_euler_product 2 3 β K

/-- Consolidated finite bosonic partition package. -/
theorem bosonic_primon_partition_synthesis :
    (∀ p β, bosonOccupationWeight p β 0 = 1) ∧
    (∀ p β k, bosonOccupationWeight p β (k + 1) =
      bosonOccupationWeight p β k * primeBoltzmannWeight p β) ∧
    (∀ p β K, singlePrimeBosonPartition p β (K + 1) =
      singlePrimeBosonPartition p β K + bosonOccupationWeight p β (K + 1)) ∧
    (∀ p q β K, singlePrimeBosonPartition p β K * singlePrimeBosonPartition q β K =
      twoPrimeBosonPartition p q β K) := by
  exact ⟨bosonOccupationWeight_zero, bosonOccupationWeight_succ,
    singlePrimeBosonPartition_succ, finite_two_prime_euler_product⟩

end noncomputable section
