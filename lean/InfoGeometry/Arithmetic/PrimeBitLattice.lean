import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-
InfoGeometry/Arithmetic/PrimeBitLattice.lean

Finite prime-bit/Fock micro-model and finite partition identity.

This file supplies a concrete arithmetic micro-model:

* finite set of allowed prime labels,
* bitstring states identified with subsets of those labels,
* bit-energy `E(ε) = Σ_{p∈ε} log p`,
* integer readout `N(ε)=∏_{p∈ε}p`,
* finite Gibbs partition identity
  `∑_{ε⊆P} exp(-β E(ε)) = ∏_{p∈P}(1+exp(-β log p))`.

The module remains theorem-safe in the sense that the statements are finite
combinatorial and model-construction identities.
-/

open scoped BigOperators

namespace InfoGeometry.Arithmetic

open Finset

noncomputable section

/-! ## 1. Data model -/

/-- A finite family of prime labels, explicitly packaged for transport. -/
abbrev PrimeBitLattice :=
  {P : Finset ℕ // ∀ p ∈ P, Nat.Prime p}

namespace PrimeBitLattice

abbrev primes (L : PrimeBitLattice) : Finset ℕ := L.1
abbrev isPrime (L : PrimeBitLattice) : ∀ p ∈ L.primes, Nat.Prime p := L.2

end PrimeBitLattice

/-- A bit-state is a finite subset of the available prime labels. -/
def PrimeBitState (L : PrimeBitLattice) :=
  {ε : Finset ℕ // ε ⊆ L.primes}

/-- Energy map `E(ε) = Σ log p` on bit-states. -/
def primeBitEnergy (_L : PrimeBitLattice) (ε : Finset ℕ) : ℝ :=
  Finset.sum ε (fun p => Real.log p)

lemma primeBitEnergy_nonneg (L : PrimeBitLattice) (ε : PrimeBitState L) :
    0 ≤ primeBitEnergy L ε.1 := by
  unfold primeBitEnergy
  exact Finset.sum_nonneg (fun p hp => by
    have hp1 : (1 : ℕ) ≤ p := le_of_lt (L.isPrime p (ε.2 hp)).one_lt
    exact Real.log_nonneg (by exact_mod_cast hp1))

/-- Integer readout `N(ε)=∏ p` on bit-states. -/
def primeBitInteger (L : PrimeBitLattice) (ε : PrimeBitState L) : ℕ :=
  Finset.prod ε.1 (fun p => p)

/-- Finite fermionic partition over all subset states. -/
def primeBitFermionicPartition (L : PrimeBitLattice) (β : ℝ) : ℝ :=
  Finset.sum (L.primes.powerset) (fun ε => Real.exp (-β * primeBitEnergy L ε))

/-- `support` projection used to read the index set of a state. -/
def PrimeBitState.support (L : PrimeBitLattice) (ε : PrimeBitState L) : Finset ℕ :=
  ε.1

/--
Energy/log-integer bridge for a fixed bit-state.

For prime states, `E(ε)=log(N(ε))`.
-/
theorem primeBitEnergy_eq_log_primeBitInteger
    {L : PrimeBitLattice} (ε : PrimeBitState L) :
    primeBitEnergy L ε.1 = Real.log (primeBitInteger L ε : ℝ) := by
  have h_ne_zero : ∀ p ∈ ε.1, (p : ℝ) ≠ 0 := by
    intro p hp
    exact_mod_cast (L.isPrime p (ε.2 hp)).ne_zero
  calc
    primeBitEnergy L ε.1
        = Finset.sum ε.1 (fun p => Real.log (p : ℝ)) := rfl
    _ = Real.log (Finset.prod ε.1 (fun p => (p : ℝ))) := (Real.log_prod h_ne_zero).symm
    _ = Real.log (primeBitInteger L ε : ℝ) := by
        rw [primeBitInteger, Nat.cast_prod]

/--
Finite partition identity over subset states.

Expanding the product `∏(1+exp(-β log p))` on the primes recovers the sum
over all occupancy states.
-/
theorem primeBitFermionicPartition_eq_factorizedProduct
  (L : PrimeBitLattice) (β : ℝ) :
    primeBitFermionicPartition L β =
      Finset.prod L.primes (fun p => (1 + Real.exp (-β * Real.log p))) := by
  classical
  rw [primeBitFermionicPartition]
  calc
    (Finset.sum (L.primes.powerset) (fun ε => Real.exp (-β * primeBitEnergy L ε)))
        = Finset.sum (L.primes.powerset) (fun ε => Finset.prod ε (fun p => Real.exp (-β * Real.log p))) := by
          refine sum_congr rfl ?_
          intro ε hε
          have hsum : -β * (Finset.sum ε (fun p => Real.log (p : ℝ))) =
              Finset.sum ε (fun p => -β * Real.log (p : ℝ)) := by
            simpa using (Finset.mul_sum ε (fun p : ℕ => Real.log (p : ℝ)) (-β))
          rw [primeBitEnergy, hsum]
          simpa using (Real.exp_sum ε (fun p : ℕ => -β * Real.log (p : ℝ)))
    _ = Finset.prod L.primes (fun p => (1 + Real.exp (-β * Real.log p))) := by
          simpa using
            (Finset.prod_one_add (s := L.primes)
              (f := fun p : ℕ => Real.exp (-β * Real.log p))).symm

/--
Equivalent factorized form using real powers `p ^ (-β)`.
-/
theorem primeBitFermionicPartition_eq_factorizedRealRpow
    (L : PrimeBitLattice) (β : ℝ) :
    primeBitFermionicPartition L β =
      Finset.prod L.primes (fun p => (1 + (p : ℝ) ^ (-β))) := by
  calc
    primeBitFermionicPartition L β = Finset.prod L.primes (fun p => (1 + Real.exp (-β * Real.log p))) :=
      primeBitFermionicPartition_eq_factorizedProduct L β
    _ = Finset.prod L.primes (fun p => (1 + (p : ℝ) ^ (-β))) := by
      refine prod_congr rfl ?_
      intro p hp
      rw [show (-β : ℝ) * Real.log p = Real.log p * (-β) by ring]
      rw [Real.exp_mul]
      have hp0 : (0 : ℝ) < p := by
        exact_mod_cast (Nat.Prime.pos (L.isPrime p (by simpa using hp))
)
      rw [Real.exp_log hp0]

lemma primeBitFermionicPartition_pos (L : PrimeBitLattice) (β : ℝ) :
    0 < primeBitFermionicPartition L β := by
  rw [primeBitFermionicPartition_eq_factorizedProduct]
  exact Finset.prod_pos (fun p _hp => by
    exact add_pos_of_pos_of_nonneg zero_lt_one (le_of_lt (Real.exp_pos _)))

lemma primeBitFermionicPartition_ne_zero (L : PrimeBitLattice) (β : ℝ) :
    primeBitFermionicPartition L β ≠ 0 :=
  (primeBitFermionicPartition_pos L β).ne'

end
end InfoGeometry.Arithmetic
