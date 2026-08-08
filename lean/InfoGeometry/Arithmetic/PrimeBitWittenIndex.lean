import Mathlib.Tactic
import InfoGeometry.Canonical.FormalPrimeRootSystem

/-!
# InfoGeometry.Arithmetic.PrimeBitWittenIndex

Finite theorem owner for the prime-bit/Witten-index Möbius parity layer.

This file owns the finite arithmetic theorem:

* a finite set of prime modes represents a squarefree integer;
* fermion number is the cardinality of the occupied prime set;
* the Möbius value of the represented squarefree integer is `(-1)^F`;
* nonsquarefree states have zero Möbius coefficient;
* the finite Boolean Witten index over a nonempty prime register cancels.

No CAR/UHF, GNS, thermodynamic limit, random-walk, Hilbert--Polya,
or analytic-continuation claim is made here.
-/

namespace InfoGeometry.Arithmetic.PrimeBitWittenIndex

open InfoGeometry.Canonical.FormalPrimeRootSystem
open scoped BigOperators
open scoped ArithmeticFunction.Moebius

/-- A finite property prime register. -/
@[rep_depth thermo]
abbrev PrimeRegister :=
  {P : Finset ℕ // ∀ p ∈ P, Nat.Prime p}

namespace PrimeRegister

abbrev primes (P : PrimeRegister) : Finset ℕ := P.1
abbrev prime_mem (P : PrimeRegister) : ∀ p ∈ P.primes, Nat.Prime p := P.2

end PrimeRegister

/--
A prime-bit state: each property prime mode is either unoccupied or occupied.

This is the explicit finite Fock/occupancy surface from Spector's construction.
The subset-register API below remains the proof-efficient form.
-/
@[rep_depth thermo]
abbrev PrimeBitState (P : PrimeRegister) :=
  {p // p ∈ P.primes} → Bool

/-- Occupied prime subset associated to a prime-bit state. -/
@[rep_depth thermo]
def occupiedPrimeSet (P : PrimeRegister) (ψ : PrimeBitState P) : Finset ℕ :=
  ((Finset.univ : Finset {p // p ∈ P.primes}).filter fun p => ψ p = true).map
    ⟨Subtype.val, by
      intro p q hpq
      exact Subtype.ext hpq⟩

/-- Occupied prime modes are a subset of the ambient register. -/
@[rep_depth thermo]
theorem occupiedPrimeSet_subset
    (P : PrimeRegister) (ψ : PrimeBitState P) :
    occupiedPrimeSet P ψ ⊆ P.primes := by
  intro p hp
  rw [occupiedPrimeSet] at hp
  rcases Finset.mem_map.mp hp with ⟨q, _hq, rfl⟩
  exact q.property

/-- The squarefree integer represented by occupied prime modes. -/
@[rep_depth thermo]
def representedNat (P : PrimeRegister) : ℕ :=
  ∏ p ∈ P.primes, p

/-- The integer represented by an occupied prime-bit state. -/
@[rep_depth thermo]
def representedNatOfState (P : PrimeRegister) (ψ : PrimeBitState P) : ℕ :=
  ∏ p ∈ occupiedPrimeSet P ψ, p

/-- Fermion number is the number of occupied prime modes. -/
@[rep_depth thermo]
def fermionNumber (P : PrimeRegister) : ℕ :=
  P.primes.card

/-- Fermion number of a prime-bit state. -/
@[rep_depth thermo]
def fermionNumberOfState (P : PrimeRegister) (ψ : PrimeBitState P) : ℕ :=
  (occupiedPrimeSet P ψ).card

/-- Fermion parity. -/
@[rep_depth thermo]
def fermionParity (P : PrimeRegister) : ℤ :=
  (-1 : ℤ) ^ fermionNumber P

/-- Fermion parity of a prime-bit state. -/
@[rep_depth thermo]
def fermionParityOfState (P : PrimeRegister) (ψ : PrimeBitState P) : ℤ :=
  (-1 : ℤ) ^ fermionNumberOfState P ψ

/-- Restrict a prime register to a subset of its occupied modes. -/
@[rep_depth thermo]
def subregister (P : PrimeRegister) (S : Finset ℕ) (hS : S ⊆ P.primes) :
    PrimeRegister :=
  ⟨S, fun p hp => P.prime_mem p (hS hp)⟩

/--
Möbius parity for a finite set of prime modes.

This is the finite Spector/Witten-index arithmetic core:
the Möbius value of a squarefree prime-bit state is the fermion parity `(-1)^F`.
-/
@[rep_depth thermo]
theorem mobius_prime_product_eq_parity
    (S : Finset ℕ) (hprime : ∀ p ∈ S, Nat.Prime p) :
    ArithmeticFunction.moebius (∏ p ∈ S, p) = (-1 : ℤ) ^ S.card := by
  classical
  calc
    ArithmeticFunction.moebius (∏ p ∈ S, p)
        = ∏ p ∈ S, ArithmeticFunction.moebius p := by
          exact
            ArithmeticFunction.isMultiplicative_moebius.map_prod_of_prime
              S hprime
    _ = ∏ _p ∈ S, (-1 : ℤ) := by
          refine Finset.prod_congr rfl ?_
          intro p hp
          exact ArithmeticFunction.moebius_apply_prime (hprime p hp)
    _ = (-1 : ℤ) ^ S.card := by
          simp

/--
Constructive Spector theorem for a property prime register.

The Möbius value of the squarefree integer represented by a finite prime-bit
state is the fermion parity `(-1)^F`.
-/
@[rep_depth thermo]
theorem mobius_representedNat_eq_fermionParity
    (P : PrimeRegister) :
    ArithmeticFunction.moebius (representedNat P) = fermionParity P := by
  simpa [representedNat, fermionParity, fermionNumber]
    using mobius_prime_product_eq_parity P.primes P.prime_mem

/--
Constructive Spector theorem for an explicit prime-bit occupancy state.

The Möbius value of the represented squarefree integer is the fermion parity
of the occupied modes.
-/
@[rep_depth thermo]
theorem mobius_representedNatOfState_eq_fermionParity
    (P : PrimeRegister) (ψ : PrimeBitState P) :
    ArithmeticFunction.moebius (representedNatOfState P ψ) =
      fermionParityOfState P ψ := by
  simpa [representedNatOfState, fermionParityOfState, fermionNumberOfState]
    using
      mobius_prime_product_eq_parity
        (occupiedPrimeSet P ψ)
        (fun p hp => P.prime_mem p (occupiedPrimeSet_subset P ψ hp))

/--
The zero clause for nonsquarefree integers is ordinary arithmetic, not a
physics property.
-/
@[rep_depth thermo]
theorem mobius_eq_zero_of_not_squarefree
    {n : ℕ} (hn : ¬ Squarefree n) :
    ArithmeticFunction.moebius n = 0 :=
  ArithmeticFunction.moebius_eq_zero_of_not_squarefree hn

/--
Finite Witten-index cancellation over a nonempty prime register.

This is the finite Boolean supertrace identity
`∑_{S ⊆ P} (-1)^|S| = 0`.
-/
@[rep_depth thermo]
theorem finite_witten_index_cancel
    (P : PrimeRegister) (hP : P.primes.Nonempty) :
    (∑ S ∈ P.primes.powerset, (-1 : ℤ) ^ S.card) = 0 := by
  classical
  exact Finset.sum_powerset_neg_one_pow_card_of_nonempty hP

/--
Finite Witten-index cancellation, state-subset form.

This is the finite supertrace over all occupied subsets of a nonempty prime
register. The explicit Bool-state API above maps into this subset surface by
`occupiedPrimeSet`.
-/
@[rep_depth thermo]
theorem finite_witten_supertrace_cancel
    (P : PrimeRegister) (hP : P.primes.Nonempty) :
    (∑ S ∈ P.primes.powerset, (-1 : ℤ) ^ S.card) = 0 :=
  finite_witten_index_cancel P hP

/--
Finite divisor Möbius cancellation:
for a nontrivial squarefree prime-bit integer, the divisor Möbius sum vanishes.
-/
@[rep_depth thermo]
theorem finite_divisor_mobius_sum_cancel
    (P : PrimeRegister) (hP : P.primes.Nonempty) :
    (∑ S ∈ P.primes.powerset,
      ArithmeticFunction.moebius (∏ p ∈ S, p)) = 0 := by
  classical
  calc
    (∑ S ∈ P.primes.powerset,
      ArithmeticFunction.moebius (∏ p ∈ S, p))
        =
      ∑ S ∈ P.primes.powerset, (-1 : ℤ) ^ S.card := by
        refine Finset.sum_congr rfl ?_
        intro S hS
        have hSub : S ⊆ P.primes := Finset.mem_powerset.mp hS
        simpa [representedNat, subregister]
        using mobius_prime_product_eq_parity S (fun p hp => P.prime_mem p (hSub hp))
    _ = 0 := finite_witten_index_cancel P hP

/-- The prime register as a finite prime root lattice. -/
@[rep_depth thermo]
def primeRootLattice (P : PrimeRegister) :
    FormalPrimeRootLattice where
  primes := P.primes
  prime_mem := P.prime_mem

/--
The finite prime Weyl denominator identity on the prime register.

This is the direct finite `A₁^P` root-system shadow of the Weyl denominator
formula, specialized to the existing prime cutoff carrier.
-/
@[rep_depth thermo]
theorem finite_prime_weyl_denominator_identity
    (P : PrimeRegister) (x : ℕ → ℝ) :
    weylDenominatorProduct
      (primeRootLattice P) x =
    weylAlternatingSum
      (primeRootLattice P) x := by
  simpa [primeRootLattice] using
    (finite_prime_weyl_denominator
      (L := primeRootLattice P) x)

end InfoGeometry.Arithmetic.PrimeBitWittenIndex
