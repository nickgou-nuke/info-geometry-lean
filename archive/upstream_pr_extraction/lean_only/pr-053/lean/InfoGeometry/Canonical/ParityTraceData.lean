import Mathlib.Tactic
import InfoGeometry.Meta.Architecture
import InfoGeometry.Canonical.FormalPrimeRootSystem
import InfoGeometry.Arithmetic.PrimeBitWittenIndex

/-!
# Finite parity trace data

Finite Boolean/exterior-state bridge between prime subsets and parity
coefficients.  The Weyl sign is attached only to square-free subset states;
the zero value on nonsquare-free integers is supplied by Mathlib's arithmetic
Möbius theorem.
-/

namespace InfoGeometry.Canonical.ParityTraceData

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

/-- Möbius coefficient used by the finite parity calculation. -/
@[rep_depth thermo]
def mobiusCoefficient (n : ℕ) : ℤ :=
  ArithmeticFunction.moebius n

/-- Absolute Möbius coefficient for the ordinary fermion trace. -/
@[rep_depth thermo]
def absMobiusCoefficient (n : ℕ) : ℕ :=
  Int.natAbs (mobiusCoefficient n)

/-- Parity-supertrace coefficient. -/
@[rep_depth thermo]
def parityCoeff (n : ℕ) : ℤ :=
  mobiusCoefficient n

/-- Ordinary fermion coefficient. -/
@[rep_depth thermo]
def fermionCoeff (n : ℕ) : ℕ :=
  absMobiusCoefficient n

/-- On the square-free subset image, the Möbius coefficient is the Weyl sign. -/
@[rep_depth thermo]
theorem mobius_squarefree_subset_eq_weyl_sign {L : FormalPrimeRootLattice}
    (S : Finset ℕ) (hS : S ⊆ L.primes) :
    mobiusCoefficient (squarefreeIntegerOfSubset S) = subsetWeylSign S := by
  have hprime : ∀ p ∈ S, Nat.Prime p := fun p hp => L.prime_mem p (hS hp)
  simpa [mobiusCoefficient, squarefreeIntegerOfSubset, subsetWeylSign]
    using mobius_prime_product_eq_parity S hprime

/-- Repeated-prime terms have zero Möbius coefficient. -/
@[rep_depth thermo]
theorem nonsquarefree_mobiusCoefficient_eq_zero
    (n : ℕ) (hn : ¬ Squarefree n) :
    mobiusCoefficient n = 0 := by
  simpa [mobiusCoefficient] using mobius_eq_zero_of_not_squarefree hn

end InfoGeometry.Canonical.ParityTraceData
