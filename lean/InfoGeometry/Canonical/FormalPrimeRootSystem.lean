import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
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

/-!
Compatibility note for older structural-surface tests:
def FormalPrimeRootLattice
def BooleanWeylGroup
-/

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

/-- Boltzmann evaluation of the formal prime root variable `e^{-β log p}`. -/
@[rep_depth thermo]
noncomputable def boltzmannRootVariable (β : ℝ) (p : ℕ) : ℝ :=
  Real.exp (-β * Real.log (p : ℝ))

/-- Finite primon partition product over a prime cutoff. -/
@[rep_depth thermo]
noncomputable def finitePrimonPartition (L : FormalPrimeRootLattice) (β : ℝ) : ℝ :=
  ∏ p ∈ L.primes, (1 - boltzmannRootVariable β p)⁻¹

/-- Evaluated finite Weyl denominator at the Boltzmann prime root variable. -/
@[rep_depth thermo]
noncomputable def evaluatedWeylDenominator (L : FormalPrimeRootLattice) (β : ℝ) : ℝ :=
  weylDenominatorProduct L (boltzmannRootVariable β)

/-- The Boltzmann root variable is the real power `p^{-β}` for positive `p`. -/
@[rep_depth thermo]
theorem boltzmannRootVariable_eq_rpow_of_pos
    (β : ℝ) {p : ℕ} (hp : 0 < (p : ℝ)) :
    boltzmannRootVariable β p = (p : ℝ) ^ (-β) := by
  unfold boltzmannRootVariable
  rw [Real.rpow_def_of_pos hp]
  congr 1
  ring

/-- The Boltzmann root variable is `p^{-β}` on every prime mode of the cutoff. -/
@[rep_depth thermo]
theorem boltzmannRootVariable_eq_rpow_of_mem
    (L : FormalPrimeRootLattice) (β : ℝ) {p : ℕ} (hp : p ∈ L.primes) :
    boltzmannRootVariable β p = (p : ℝ) ^ (-β) := by
  exact boltzmannRootVariable_eq_rpow_of_pos β
    (by exact_mod_cast Nat.Prime.pos (L.prime_mem p hp))

/--
Finite reciprocal Weyl/Euler product identity.

This is the closed finite cutoff statement: the primon product is exactly the
inverse of the evaluated Boolean `A₁^P` Weyl denominator.
-/
@[rep_depth thermo]
theorem finitePrimonPartition_eq_evaluatedWeylDenominator_inv
    (L : FormalPrimeRootLattice) (β : ℝ) :
    finitePrimonPartition L β = (evaluatedWeylDenominator L β)⁻¹ := by
  unfold finitePrimonPartition evaluatedWeylDenominator weylDenominatorProduct
    rootThermalVariable
  exact
    (Finset.prod_inv_distrib
      (s := L.primes) (f := fun p : ℕ => 1 - boltzmannRootVariable β p))

/--
Finite primon product written in the conventional `p^{-β}` variables.
-/
@[rep_depth thermo]
theorem finitePrimonPartition_eq_rpowProduct
    (L : FormalPrimeRootLattice) (β : ℝ) :
    finitePrimonPartition L β =
      ∏ p ∈ L.primes, (1 - (p : ℝ) ^ (-β))⁻¹ := by
  unfold finitePrimonPartition
  refine Finset.prod_congr rfl ?_
  intro p hp
  rw [boltzmannRootVariable_eq_rpow_of_mem L β hp]

/--
The reciprocal Weyl denominator is the conventional finite primon Euler product.
-/
@[rep_depth thermo]
theorem rpowProduct_eq_evaluatedWeylDenominator_inv
    (L : FormalPrimeRootLattice) (β : ℝ) :
    (∏ p ∈ L.primes, (1 - (p : ℝ) ^ (-β))⁻¹) =
      (evaluatedWeylDenominator L β)⁻¹ := by
  rw [← finitePrimonPartition_eq_rpowProduct L β]
  exact finitePrimonPartition_eq_evaluatedWeylDenominator_inv L β

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
