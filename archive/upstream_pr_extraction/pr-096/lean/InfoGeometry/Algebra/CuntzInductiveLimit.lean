import Mathlib.Tactic
import InfoGeometry.Algebra.CuntzTensorQuotient

/-!
# Finite-stage Cuntz inductive-limit readouts

This file does not construct a C*-completion of `O_∞` and does not claim a
trace-class theorem for an infinite Hamiltonian.  It records the theorem-backed
finite-stage Cuntz/Toeplitz relations that any later inductive-limit
construction must preserve, delegating the quotient presentation to
`InfoGeometry.Algebra.CuntzTensorQuotient`.
-/

open scoped BigOperators

noncomputable section

namespace InfoGeometry.Algebra.CuntzInductiveLimit

open InfoGeometry.Algebra.CuntzTensorQuotient

/-!
The finite Cuntz and Toeplitz generators and their quotient relations are
owned directly by `CuntzTensorQuotient`.  This module therefore does not
duplicate stage aliases or forwarding packets; later colimit constructions
use `cuntzS`, `cuntzSdag`, `toeplitzS`, `toeplitzSdag`, and the native quotient
lemmas directly.
-/

/-- The fermionic partition function for the first `n` indexed prime modes. -/
def fermionicPartitionTruncated (n : ℕ) (primes : ℕ → ℕ) (β : ℝ) : ℝ :=
  Finset.prod (Finset.range n) fun i => (1 : ℝ) + ((primes i : ℝ) ^ (-β))

/--
Finite-stage positivity of the fermionic partition factors for prime modes at
positive inverse temperature.  This is the theorem-safe finite readout; no
infinite Euler-product convergence is asserted here.
-/
theorem fermionicPartitionTruncated_pos
    (primes : ℕ → ℕ) (hprime : ∀ i, Nat.Prime (primes i)) (β : ℝ) (_hβ : 0 < β) :
    ∀ n : ℕ, 0 < fermionicPartitionTruncated n primes β := by
  intro n
  unfold fermionicPartitionTruncated
  refine Finset.prod_pos (fun i _hi => ?_)
  have hp_pos : 0 < (primes i : ℝ) := by
    exact_mod_cast (hprime i).pos
  have hpow_pos : 0 < (primes i : ℝ) ^ (-β) :=
    Real.rpow_pos_of_pos hp_pos (-β)
  exact add_pos zero_lt_one hpow_pos

/-- The old β > 1 interface reduced to the finite positivity readout. -/
theorem fermionicPartition_converges
    (primes : ℕ → ℕ) (hprime : ∀ i, Nat.Prime (primes i)) (β : ℝ) (hβ : 1 < β) :
    0 < β ∧ ∀ n : ℕ, 0 < fermionicPartitionTruncated n primes β := by
  have hβpos : 0 < β := by linarith
  refine ⟨?_, ?_⟩
  · exact hβpos
  · exact fermionicPartitionTruncated_pos primes hprime β hβpos

end InfoGeometry.Algebra.CuntzInductiveLimit
