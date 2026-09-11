import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Data.Nat.Squarefree
import InfoGeometry.Arithmetic.PrimeBitLattice
import InfoGeometry.Arithmetic.PrimeBitWittenIndex

noncomputable section

open scoped ArithmeticFunction.Moebius

namespace InfoGeometry.Arithmetic.PrimeBitMobiusParityBridge

open InfoGeometry.Arithmetic

theorem primeBitInteger_ne_zero
    {L : PrimeBitLattice} (ε : PrimeBitState L) :
    primeBitInteger L ε ≠ 0 := by
  unfold primeBitInteger
  refine Finset.prod_ne_zero_iff.mpr ?_
  intro p hp
  exact (L.isPrime p (ε.property hp)).ne_zero

theorem primeBitInteger_squarefree
    {L : PrimeBitLattice} (ε : PrimeBitState L) :
    Squarefree (primeBitInteger L ε) := by
  unfold primeBitInteger
  refine Finset.squarefree_prod_of_pairwise_isCoprime ?_ ?_
  · intro p hp q hq hpq
    have hpp : Nat.Prime p := L.isPrime p (ε.property hp)
    have hqq : Nat.Prime q := L.isPrime q (ε.property hq)
    simpa [Function.onFun, Nat.coprime_iff_isRelPrime] using
      ((Nat.coprime_primes hpp hqq).2 hpq)
  · intro p hp
    exact (L.isPrime p (ε.property hp)).squarefree

theorem primeBitInteger_primeFactors
    {L : PrimeBitLattice} (ε : PrimeBitState L) :
    (primeBitInteger L ε).primeFactorsList.toFinset = ε.1 := by
  apply Finset.ext
  intro p
  constructor
  · intro hp
    rw [List.mem_toFinset] at hp
    rw [Nat.mem_primeFactorsList (primeBitInteger_ne_zero ε)] at hp
    have hpprime : Nat.Prime p := hp.1
    have hpdiv : p ∣ primeBitInteger L ε := hp.2
    rw [primeBitInteger, hpprime.prime.dvd_finset_prod_iff] at hpdiv
    rcases hpdiv with ⟨a, ha, hpa⟩
    have haprime : Nat.Prime a := L.isPrime a (ε.property ha)
    have heq : a = p :=
      (Nat.Prime.dvd_iff_eq haprime hpprime.ne_one).mp hpa
    subst heq
    exact ha
  · intro hp
    rw [List.mem_toFinset]
    rw [Nat.mem_primeFactorsList (primeBitInteger_ne_zero ε)]
    have hpprime : Nat.Prime p := L.isPrime p (ε.property hp)
    exact ⟨hpprime, Finset.dvd_prod_of_mem (fun x => x) hp⟩

theorem primeBitInteger_card_primeFactors
    {L : PrimeBitLattice} (ε : PrimeBitState L) :
    (primeBitInteger L ε).primeFactorsList.toFinset.card = ε.1.card := by
  rw [primeBitInteger_primeFactors]

theorem mobius_primeBitInteger_eq_parity
    {L : PrimeBitLattice} (ε : PrimeBitState L) :
    ArithmeticFunction.moebius (primeBitInteger L ε) =
      (-1 : ℤ) ^ ε.1.card := by
  exact PrimeBitWittenIndex.mobius_prime_product_eq_parity ε.1
    (fun p hp => L.isPrime p (ε.property hp))

theorem mobius_primeBitInteger_eq_parity_sign
    {L : PrimeBitLattice} (ε : PrimeBitState L) :
    ArithmeticFunction.moebius (primeBitInteger L ε) =
      (-1 : ℤ) ^ (PrimeBitState.support L ε).card := by
  exact mobius_primeBitInteger_eq_parity ε

end InfoGeometry.Arithmetic.PrimeBitMobiusParityBridge
