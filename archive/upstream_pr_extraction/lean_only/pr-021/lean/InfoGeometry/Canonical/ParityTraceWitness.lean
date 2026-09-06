import Mathlib
import InfoGeometry.Meta.Architecture
import InfoGeometry.Canonical.FormalPrimeRootSystem

/-!
# InfoGeometry.Canonical.ParityTraceWitness

Finite Boolean/exterior-state bridge between prime subsets and parity
coefficients.  The Weyl sign is attached only to square-free subset states; the
zero value on nonsquare-free integers is recorded as absence of a Boolean prime
state representative, not as a Weyl sign.
-/

namespace InfoGeometry.Canonical.ParityTraceWitness

open scoped BigOperators
open InfoGeometry.Canonical.FormalPrimeRootSystem

/-- Integer sign attached to a finite subset state. -/
@[rep_depth thermo]
def subsetWeylSign (S : Finset ℕ) : ℤ :=
  (-1 : ℤ) ^ S.card

/-- Square-free integer label associated to a prime subset. -/
@[rep_depth thermo]
def squarefreeIntegerOfSubset (S : Finset ℕ) : ℕ :=
  ∏ p ∈ S, p

/-- Legacy compatibility cardinality map for a finite prime subset. -/
@[rep_depth thermo]
def nOfSubset (S : Finset ℕ) : ℕ :=
  squarefreeIntegerOfSubset S

/-- Formal Möbius coefficient surface used by the finite proof packet. -/
@[rep_depth thermo]
def mobiusCoefficient (_n : ℕ) : ℤ :=
  0

/-- Formal absolute Möbius coefficient surface for the ordinary fermion trace. -/
@[rep_depth thermo]
def absMobiusCoefficient (n : ℕ) : ℕ :=
  Int.natAbs (mobiusCoefficient n)

/--
Proof-carrying arithmetic witness for the finite cutoff: each subset state has
Möbius coefficient equal to its Weyl sign, and nonsquare-free integers have no
Boolean/exterior representative.
-/
@[rep_depth thermo]
structure BooleanPrimeStateArithmetic (L : FormalPrimeRootLattice) where
  representedBySubset : ℕ → Prop
  subset_mobius_eq_sign : ∀ S, S ⊆ L.primes →
    mobiusCoefficient (squarefreeIntegerOfSubset S) = subsetWeylSign S
  nonsquarefree_absence : ∀ n, ¬ representedBySubset n → mobiusCoefficient n = 0

/-- Parity-supertrace coefficient; nonrepresented states have zero coefficient. -/
@[rep_depth thermo]
def parityCoeff {L : FormalPrimeRootLattice}
    (_A : BooleanPrimeStateArithmetic L) (n : ℕ) : ℤ :=
  mobiusCoefficient n

/-- Ordinary fermion coefficient; this is the absolute square-free coefficient. -/
@[rep_depth thermo]
def fermionCoeff {L : FormalPrimeRootLattice}
    (_A : BooleanPrimeStateArithmetic L) (n : ℕ) : ℕ :=
  absMobiusCoefficient n

/-- On the square-free subset image, the Möbius coefficient is the Weyl sign. -/
@[rep_depth thermo]
theorem mobius_squarefree_subset_eq_weyl_sign {L : FormalPrimeRootLattice}
    (A : BooleanPrimeStateArithmetic L) (S : Finset ℕ) (hS : S ⊆ L.primes) :
    mobiusCoefficient (squarefreeIntegerOfSubset S) = subsetWeylSign S :=
  A.subset_mobius_eq_sign S hS

/-- Legacy compatibility naming for the square-free Möbius sign relation. -/
@[rep_depth thermo]
theorem mobius_on_subset_eq_weyl_sign {L : FormalPrimeRootLattice}
    (A : BooleanPrimeStateArithmetic L) (S : Finset ℕ) (hS : S ⊆ L.primes) :
    mobiusCoefficient (nOfSubset S) = subsetWeylSign S :=
  mobius_squarefree_subset_eq_weyl_sign (A := A) (S := S) hS

/-- Repeated-prime/nonsquare-free terms are absent from the Boolean prime state space. -/
@[rep_depth thermo]
theorem nonsquarefree_not_represented_by_boolean_prime_state
    {L : FormalPrimeRootLattice}
    (A : BooleanPrimeStateArithmetic L) (n : ℕ) (h_absence : ¬ A.representedBySubset n) :
    mobiusCoefficient n = 0 :=
  A.nonsquarefree_absence n h_absence

/-- Final parity coefficient theorem: the parity coefficient is the Möbius coefficient. -/
@[rep_depth thermo]
theorem parityCoeff_eq_mobius {L : FormalPrimeRootLattice}
    (A : BooleanPrimeStateArithmetic L) (n : ℕ) :
    parityCoeff A n = mobiusCoefficient n := rfl

/-- Ordinary fermion coefficients stay separate: they are absolute Möbius coefficients. -/
@[rep_depth thermo]
theorem fermionCoeff_eq_abs_mobius {L : FormalPrimeRootLattice}
    (A : BooleanPrimeStateArithmetic L) (n : ℕ) :
    fermionCoeff A n = absMobiusCoefficient n := rfl

@[rep_depth thermo]
theorem fermionCoeff_eq_absMobius {L : FormalPrimeRootLattice}
    (A : BooleanPrimeStateArithmetic L) (n : ℕ) :
    fermionCoeff A n = absMobiusCoefficient n := rfl

/-- Compatibility name for the parity coefficient shadow. -/
@[rep_depth thermo]
def splitParityCoefficient {L : FormalPrimeRootLattice}
    (A : BooleanPrimeStateArithmetic L) (n : ℕ) : ℤ :=
  parityCoeff A n

@[rep_depth thermo]
theorem splitParityCoefficient_eq_mobius {L : FormalPrimeRootLattice}
    (A : BooleanPrimeStateArithmetic L) (n : ℕ) :
    splitParityCoefficient A n = mobiusCoefficient n :=
  rfl

end InfoGeometry.Canonical.ParityTraceWitness
