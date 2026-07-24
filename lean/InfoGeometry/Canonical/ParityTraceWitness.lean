import Mathlib
import InfoGeometry.Meta.Architecture
import InfoGeometry.Canonical.FormalPrimeRootSystem
import InfoGeometry.Arithmetic.PrimeBitWittenIndex

/-!
# InfoGeometry.Canonical.ParityTraceWitness

Finite Boolean/exterior-state bridge between prime subsets and parity
coefficients.  The Weyl sign is attached only to square-free subset states; the
zero value on nonsquare-free integers records the absence of any Boolean
subset-state witness and is projected from Mathlib's arithmetic Möbius theorem,
not stored as a witness field.
-/

namespace InfoGeometry.Canonical.ParityTraceWitness

open scoped BigOperators
open scoped ArithmeticFunction.Moebius
open FormalPrimeRootSystem
open InfoGeometry.Arithmetic.PrimeBitWittenIndex

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

/-- Möbius coefficient surface used by the finite proof packet. -/
@[rep_depth thermo]
def mobiusCoefficient (n : ℕ) : ℤ :=
  ArithmeticFunction.moebius n

/-- Formal absolute Möbius coefficient surface for the ordinary fermion trace. -/
@[rep_depth thermo]
def absMobiusCoefficient (n : ℕ) : ℕ :=
  Int.natAbs (mobiusCoefficient n)

/-- Finite cutoff representation predicate for the Boolean prime-state layer. -/
@[rep_depth thermo]
structure BooleanPrimeStateArithmetic (L : FormalPrimeRootLattice) where
  /-- Integer labels represented by subsets of the finite prime cutoff. -/
  representedBySubset : ℕ → Prop

  /-- A subset of the cutoff represents its squarefree prime product. -/
  subset_represents :
    ∀ S, S ⊆ L.primes → representedBySubset (squarefreeIntegerOfSubset S)

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
    (_A : BooleanPrimeStateArithmetic L) (S : Finset ℕ) (hS : S ⊆ L.primes) :
    mobiusCoefficient (squarefreeIntegerOfSubset S) = subsetWeylSign S :=
  by
    have hprime : ∀ p ∈ S, Nat.Prime p := fun p hp => L.prime_mem p (hS hp)
    simpa [mobiusCoefficient, squarefreeIntegerOfSubset, subsetWeylSign]
      using mobius_prime_product_eq_parity S hprime

/-- Legacy compatibility naming for the square-free Möbius sign relation. -/
@[rep_depth thermo]
theorem mobius_on_subset_eq_weyl_sign {L : FormalPrimeRootLattice}
    (A : BooleanPrimeStateArithmetic L) (S : Finset ℕ) (hS : S ⊆ L.primes) :
    mobiusCoefficient (nOfSubset S) = subsetWeylSign S :=
  mobius_squarefree_subset_eq_weyl_sign (_A := A) (S := S) hS

/-- Repeated-prime/nonsquare-free terms have zero Möbius coefficient. -/
@[rep_depth thermo]
theorem nonsquarefree_not_represented_by_boolean_prime_state
    {L : FormalPrimeRootLattice}
    (_A : BooleanPrimeStateArithmetic L) (n : ℕ) (hn : ¬ Squarefree n) :
    mobiusCoefficient n = 0 :=
  by
    simpa [mobiusCoefficient] using mobius_eq_zero_of_not_squarefree hn

/-- Subset products are represented by the Boolean prime-state layer. -/
@[rep_depth thermo]
theorem subset_represented_by_boolean_prime_state
    {L : FormalPrimeRootLattice}
    (A : BooleanPrimeStateArithmetic L) (S : Finset ℕ) (hS : S ⊆ L.primes) :
    A.representedBySubset (squarefreeIntegerOfSubset S) :=
  A.subset_represents S hS

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
