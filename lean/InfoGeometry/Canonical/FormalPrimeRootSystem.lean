import Mathlib
import InfoGeometry.Meta.Architecture

/-!
# InfoGeometry.Canonical.FormalPrimeRootSystem

Finite prime cutoff root-system layer for the corrected Souriau-Weyl
supertrace corridor.

The root system is the finite Boolean `A₁^P` model: one formal root `α_p` for
each rational prime in a finite cutoff `P`, with Weyl elements represented by
subsets of `P`.  This file proves the finite denominator identity as a direct
`Finset.prod_sub` combinatorial expansion.
-/

namespace InfoGeometry.Canonical.FormalPrimeRootSystem

open scoped BigOperators

/-- Finite family of primes with explicit primality proof for every member. -/
@[rep_depth thermo]
structure FinitePrimeSet where
  primes : Finset ℕ
  prime_mem : ∀ p ∈ primes, Nat.Prime p

/-- Formal root lattice carrier for a finite prime cutoff. -/
@[rep_depth thermo]
structure FormalPrimeRootLattice where
  primes : Finset ℕ
  prime_mem : ∀ p ∈ primes, Nat.Prime p

/-- Boolean Weyl group element: a subset of the finite prime cutoff. -/
@[rep_depth thermo]
structure BooleanWeylGroup (L : FormalPrimeRootLattice) where
  support : Finset ℕ
  support_subset : support ⊆ L.primes

/-- Finite `A₁^P` root system, deliberately only the Boolean prime-mode cutoff. -/
@[rep_depth thermo]
structure PrimeA1RootSystem where
  lattice : FormalPrimeRootLattice

/-- Formal half-sum of positive roots, represented by its finite support. -/
@[rep_depth thermo]
def rho_P (R : PrimeA1RootSystem) : Finset ℕ :=
  R.lattice.primes

/-- Weyl sign character `ε(w_S) = (-1)^{|S|}`. -/
@[rep_depth thermo]
def weylSign {L : FormalPrimeRootLattice} (w : BooleanWeylGroup L) : ℝ :=
  (-1 : ℝ) ^ w.support.card

/-- Evaluated root variable `e^{-α_p}` supplied by an external thermal evaluation. -/
@[rep_depth thermo]
def rootThermalVariable (_L : FormalPrimeRootLattice) (x : ℕ → ℝ) (p : ℕ) : ℝ :=
  x p

/-- Finite Weyl-denominator/product side `∏_{p∈P} (1 - e^{-α_p})`. -/
@[rep_depth thermo]
def weylDenominatorProduct (L : FormalPrimeRootLattice) (x : ℕ → ℝ) : ℝ :=
  ∏ p ∈ L.primes, (1 - rootThermalVariable L x p)

/-- Alternating subset expansion `∑_{S⊆P} (-1)^{|S|} ∏_{p∈S} e^{-α_p}`. -/
@[rep_depth thermo]
def weylAlternatingSum (L : FormalPrimeRootLattice) (x : ℕ → ℝ) : ℝ :=
  ∑ S ∈ L.primes.powerset, ((-1 : ℝ) ^ S.card) * ∏ p ∈ S, rootThermalVariable L x p

/--
Finite prime-mode Weyl denominator identity.

This is the manuscript-safe algebraic core: the denominator-like object is the
alternating product/supertrace, and the proof is purely finite combinatorics.
-/
@[rep_depth thermo]
theorem finite_prime_weyl_denominator
    (L : FormalPrimeRootLattice) (x : ℕ → ℝ) :
    weylDenominatorProduct L x = weylAlternatingSum L x := by
  classical
  unfold weylDenominatorProduct weylAlternatingSum rootThermalVariable
  simpa using (Finset.prod_sub (fun _ : ℕ => (1 : ℝ)) x L.primes)

@[rep_depth thermo]
theorem finite_denominator_identity
    (L : FormalPrimeRootLattice) (x : ℕ → ℝ) :
    weylDenominatorProduct L x = weylAlternatingSum L x :=
  finite_prime_weyl_denominator L x

end InfoGeometry.Canonical.FormalPrimeRootSystem
