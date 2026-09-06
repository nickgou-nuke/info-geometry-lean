import Mathlib.Tactic
import InfoGeometry.Canonical.FormalPrimeRootSystem

namespace InfoGeometry.Arithmetic.PrimeBitWittenIndex

open InfoGeometry.Canonical.FormalPrimeRootSystem
open scoped BigOperators
open scoped ArithmeticFunction.Moebius

@[rep_depth thermo]
abbrev PrimeRegister :=
  {P : Finset ℕ // ∀ p ∈ P, Nat.Prime p}

namespace PrimeRegister

abbrev primes (P : PrimeRegister) : Finset ℕ := P.1
abbrev prime_mem (P : PrimeRegister) : ∀ p ∈ P.primes, Nat.Prime p := P.2

end PrimeRegister

@[rep_depth thermo]
abbrev PrimeBitState (P : PrimeRegister) :=
  {p // p ∈ P.primes} → Bool

@[rep_depth thermo]
def occupiedPrimeSet (P : PrimeRegister) (ψ : PrimeBitState P) : Finset ℕ :=
  ((Finset.univ : Finset {p // p ∈ P.primes}).filter fun p => ψ p = true).map
    ⟨Subtype.val, by
      intro p q hpq
      exact Subtype.ext hpq⟩

@[rep_depth thermo]
theorem occupiedPrimeSet_subset
    (P : PrimeRegister) (ψ : PrimeBitState P) :
    occupiedPrimeSet P ψ ⊆ P.primes := by
  intro p hp
  rw [occupiedPrimeSet] at hp
  rcases Finset.mem_map.mp hp with ⟨q, _hq, rfl⟩
  exact q.property

@[rep_depth thermo]
def representedNat (P : PrimeRegister) : ℕ :=
  ∏ p ∈ P.primes, p

@[rep_depth thermo]
def representedNatOfState (P : PrimeRegister) (ψ : PrimeBitState P) : ℕ :=
  ∏ p ∈ occupiedPrimeSet P ψ, p

@[rep_depth thermo]
def fermionNumber (P : PrimeRegister) : ℕ :=
  P.primes.card

@[rep_depth thermo]
def fermionNumberOfState (P : PrimeRegister) (ψ : PrimeBitState P) : ℕ :=
  (occupiedPrimeSet P ψ).card

@[rep_depth thermo]
def fermionParity (P : PrimeRegister) : ℤ :=
  (-1 : ℤ) ^ fermionNumber P

@[rep_depth thermo]
def fermionParityOfState (P : PrimeRegister) (ψ : PrimeBitState P) : ℤ :=
  (-1 : ℤ) ^ fermionNumberOfState P ψ

@[rep_depth thermo]
def subregister (P : PrimeRegister) (S : Finset ℕ) (hS : S ⊆ P.primes) :
    PrimeRegister :=
  ⟨S, fun p hp => P.prime_mem p (hS hp)⟩

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

@[rep_depth thermo]
theorem mobius_representedNat_eq_fermionParity
    (P : PrimeRegister) :
    ArithmeticFunction.moebius (representedNat P) = fermionParity P := by
  simpa [representedNat, fermionParity, fermionNumber]
    using mobius_prime_product_eq_parity P.primes P.prime_mem

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

@[rep_depth thermo]
theorem mobius_eq_zero_of_not_squarefree
    {n : ℕ} (hn : ¬ Squarefree n) :
    ArithmeticFunction.moebius n = 0 :=
  ArithmeticFunction.moebius_eq_zero_of_not_squarefree hn

@[rep_depth thermo]
theorem finite_witten_index_cancel
    (P : PrimeRegister) (hP : P.primes.Nonempty) :
    (∑ S ∈ P.primes.powerset, (-1 : ℤ) ^ S.card) = 0 := by
  classical
  exact Finset.sum_powerset_neg_one_pow_card_of_nonempty hP

@[rep_depth thermo]
theorem finite_witten_supertrace_cancel
    (P : PrimeRegister) (hP : P.primes.Nonempty) :
    (∑ S ∈ P.primes.powerset, (-1 : ℤ) ^ S.card) = 0 :=
  finite_witten_index_cancel P hP

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

@[rep_depth thermo]
def primeRootLattice (P : PrimeRegister) :
    FormalPrimeRootLattice where
  primes := P.primes
  prime_mem := P.prime_mem

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
