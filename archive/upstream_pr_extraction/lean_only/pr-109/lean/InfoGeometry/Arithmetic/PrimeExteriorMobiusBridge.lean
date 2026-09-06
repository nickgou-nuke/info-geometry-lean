import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic.Basic
import InfoGeometry.Arithmetic.PrimeExteriorRepresentation
import InfoGeometry.Arithmetic.PrimeBitWittenIndex
import InfoGeometry.Arithmetic.PrimeCantorLatticeDirac


noncomputable section

open scoped BigOperators
open scoped ArithmeticFunction.Moebius

namespace InfoGeometry.Arithmetic.PrimeExteriorMobiusBridge

open InfoGeometry.Arithmetic.PrimeExteriorRepresentation
open InfoGeometry.Arithmetic.PrimeBitWittenIndex

abbrev PrimeCutoff := PrimeRegister

abbrev PrimeMode (P : PrimeCutoff) :=
  {p : ℕ // p ∈ P.primes}

def primeModeEmbedding (P : PrimeCutoff) : PrimeMode P ↪ ℕ :=
  ⟨Subtype.val, by
    intro a b h
    exact Subtype.ext h⟩

abbrev SquareFreeState (P : PrimeCutoff) :=
  SquareFreePrimeState (PrimeMode P)

def natSetOfState {P : PrimeCutoff} (S : SquareFreeState P) : Finset ℕ :=
  S.map (primeModeEmbedding P)

theorem natSetOfState_prime_mem
    {P : PrimeCutoff}
    (S : SquareFreeState P) :
    ∀ n ∈ natSetOfState S, Nat.Prime n := by
  intro n hn
  unfold natSetOfState at hn
  rcases Finset.mem_map.mp hn with ⟨p, _hp, rfl⟩
  exact P.prime_mem p.1 p.property

def stateNat {P : PrimeCutoff} (S : SquareFreeState P) : ℕ :=
  ∏ n ∈ natSetOfState S, n

theorem card_natSetOfState
    {P : PrimeCutoff}
    (S : SquareFreeState P) :
    (natSetOfState S).card = S.card := by
  unfold natSetOfState
  exact Finset.card_map (primeModeEmbedding P)

theorem stateNat_squarefree
    {P : PrimeCutoff}
    (S : SquareFreeState P) :
    Squarefree (stateNat S) := by
  unfold stateNat
  refine Finset.squarefree_prod_of_pairwise_isCoprime ?_ ?_
  · intro x hx y hy hxy
    have hx' : Nat.Prime x := natSetOfState_prime_mem S x hx
    have hy' : Nat.Prime y := natSetOfState_prime_mem S y hy
    simpa [Nat.coprime_iff_isRelPrime] using
      ((Nat.coprime_primes hx' hy').2 hxy)
  · intro x hx
    exact (natSetOfState_prime_mem S x hx).squarefree

theorem stateNat_pos
    {P : PrimeCutoff}
    (S : SquareFreeState P) :
    0 < stateNat S := by
  unfold stateNat
  exact Finset.prod_pos (fun n hn => (natSetOfState_prime_mem S n hn).pos)

/-- The logarithmic energy of the encoded square-free integer is the
    exterior square-free energy of its occupied prime modes. -/
theorem stateNat_log_eq_squareFreeEnergy
    {P : PrimeCutoff}
    (S : SquareFreeState P) :
    Real.log (stateNat S : ℝ) =
      SquareFreePrimeState.squareFreeEnergy
        (fun p : PrimeMode P => Real.log (p.1 : ℝ)) S := by
  have h_ne_zero : ∀ n ∈ natSetOfState S, (n : ℝ) ≠ 0 := by
    intro n hn
    exact_mod_cast (natSetOfState_prime_mem S n hn).ne_zero
  unfold stateNat SquareFreePrimeState.squareFreeEnergy
  rw [Nat.cast_prod, Real.log_prod h_ne_zero]
  unfold natSetOfState
  rw [Finset.sum_map]
  apply Finset.sum_congr rfl
  intro p hp
  rfl

theorem mobius_stateNat_eq_fermionParitySign
    {P : PrimeCutoff}
    (S : SquareFreeState P) :
    ArithmeticFunction.moebius (stateNat S) =
      SquareFreePrimeState.fermionParitySign S := by
  have hprime : ∀ n ∈ natSetOfState S, Nat.Prime n :=
    natSetOfState_prime_mem S
  simpa [stateNat, SquareFreePrimeState.fermionParitySign, card_natSetOfState] using
    (PrimeBitWittenIndex.mobius_prime_product_eq_parity (natSetOfState S) hprime)

theorem mobius_stateNat_eq_Gamma
    {P : PrimeCutoff}
    (S : SquareFreeState P) :
    ArithmeticFunction.moebius (stateNat S) = SquareFreePrimeState.Gamma S := by
  simp [SquareFreePrimeState.Gamma, mobius_stateNat_eq_fermionParitySign]

end InfoGeometry.Arithmetic.PrimeExteriorMobiusBridge
