import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Arithmetic.PrimeParafermionGrandCanonicalClock
import InfoGeometry.Arithmetic.ChiralPrimonGas
import InfoGeometry.Arithmetic.PrimeBosonFermionGas
import InfoGeometry.Arithmetic.PrimeOccupationAlgebra
import InfoGeometry.Arithmetic.PrimeGrandCanonicalEnsemble
import InfoGeometry.Categorical.PrimeThermodynamicReadoutCones

noncomputable section

namespace InfoGeometry.Categorical.PrimeThermodynamicStateEquivalence

open InfoGeometry.Arithmetic.PrimeOccupationAlgebra
open InfoGeometry.Arithmetic.ChiralPrimonGas
open InfoGeometry.Arithmetic.PrimeGrandCanonicalEnsemble
open InfoGeometry.Arithmetic.PrimeParafermionGrandCanonicalClock
open InfoGeometry.Arithmetic.PrimeBosonFermionGas
open InfoGeometry.Categorical.PrimeThermodynamicReadoutCones
open scoped BigOperators

@[rep_depth thermo]
abbrev ExponentVector (n : ℕ) :=
  (p : primesUpto n) → ℕ

@[rep_depth thermo]
def encodeToNaturalNumber (n : ℕ) (v : ExponentVector n) : ℕ :=
  ∏ p : primesUpto n, (p.1 ^ v p)

theorem encodeToNaturalNumber_energy_preservation (n : ℕ) (v : ExponentVector n) :
    Real.log (encodeToNaturalNumber n v) =
      ∑ p : primesUpto n, ((v p) : ℝ) * Real.log (p.1 : ℝ) := by
  unfold encodeToNaturalNumber
  rw [Nat.cast_prod]
  rw [Real.log_prod]
  · apply Finset.sum_congr rfl
    intro p _hp
    have hprime := (mem_primesUpto_iff.mp p.2).2
    have hp_pos : 0 < p.1 := Nat.Prime.pos hprime
    have hp_real_pos : (0 : ℝ) < p.1 := by exact_mod_cast hp_pos
    rw [Nat.cast_pow]
    rw [log_pow_nat_of_pos _ _ hp_real_pos]
  · intro p _hp
    have hprime := (mem_primesUpto_iff.mp p.2).2
    have hp_pos : 0 < p.1 := Nat.Prime.pos hprime
    have hp_pow_pos : 0 < p.1 ^ (v p) := pow_pos hp_pos _
    rw [Nat.cast_pow]
    exact ne_of_gt (by exact_mod_cast hp_pow_pos)

def stateSum (n : ℕ) (κ : ℕ) (z s : ℂ) : ℂ :=
  ∑ v ∈ Fintype.piFinset (fun _p : primesUpto n => Finset.range κ),
    ∏ p : primesUpto n, grandComplexPrimeWeight z s (toNatPrimes p) ^ (v p)

def primeMode (n : ℕ) (κ : ℕ) (z s : ℂ) : ℂ :=
  ∏ p : primesUpto n, ∑ i ∈ Finset.range κ, grandComplexPrimeWeight z s (toNatPrimes p) ^ i

theorem primeMode_eq_stateSum (n : ℕ) (κ : ℕ) (z s : ℂ) :
    primeMode n κ z s = stateSum n κ z s := by
  unfold primeMode stateSum
  exact Finset.prod_univ_sum (fun _p => Finset.range κ)
    (fun p i => grandComplexPrimeWeight z s (toNatPrimes p) ^ i)

theorem primeMode_derivedReadout_eq_stateSum_derivedReadout
    (n : ℕ) (κ : ℕ) (z s : ℂ) (D : ℂ → ℂ) :
    D (primeMode n κ z s) = D (stateSum n κ z s) := by
  rw [primeMode_eq_stateSum n κ z s]

end InfoGeometry.Categorical.PrimeThermodynamicStateEquivalence
