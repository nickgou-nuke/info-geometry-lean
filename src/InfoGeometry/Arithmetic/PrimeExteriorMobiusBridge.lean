import Mathlib.Data.Finset.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic.Basic
import InfoGeometry.Arithmetic.PrimeExteriorRepresentation
import InfoGeometry.Arithmetic.PrimeBitWittenIndex
import InfoGeometry.Arithmetic.PrimeCantorLatticeDirac

/-!
# InfoGeometry.Arithmetic.PrimeExteriorMobiusBridge

Native bridge from the canonical finite exterior carrier to the existing
Möbius/Witten parity theorem.

This file closes the finite arithmetic parity readout for the canonical
prime-cube surfaces.

No infinite Euler product.
No analytic continuation.
No Hilbert--Polya/RH claim.
-/

noncomputable section

open scoped BigOperators
open scoped ArithmeticFunction.Moebius

namespace InfoGeometry.Arithmetic.PrimeExteriorMobiusBridge

open InfoGeometry.Arithmetic.PrimeExteriorRepresentation
open InfoGeometry.Arithmetic.PrimeBitWittenIndex

/-- A finite prime cutoff, using the existing certified prime register. -/
abbrev PrimeCutoff := PrimeRegister

/-- A prime mode inside a finite cutoff. -/
abbrev PrimeMode (P : PrimeCutoff) :=
  {p : ℕ // p ∈ P.primes}

/-- A prime mode embedding into `ℕ`. -/
def primeModeEmbedding (P : PrimeCutoff) : PrimeMode P ↪ ℕ :=
  ⟨Subtype.val, by
    intro a b h
    exact Subtype.ext h⟩

/-- The canonical finite exterior carrier over a prime cutoff. -/
abbrev SquareFreeState (P : PrimeCutoff) :=
  SquareFreePrimeState (PrimeMode P)

/-- Underlying natural-number set of a square-free exterior state. -/
def natSetOfState {P : PrimeCutoff} (S : SquareFreeState P) : Finset ℕ :=
  S.map (primeModeEmbedding P)

/-- Elements of `natSetOfState` are prime. -/
theorem natSetOfState_prime_mem
    {P : PrimeCutoff}
    (S : SquareFreeState P) :
    ∀ n ∈ natSetOfState S, Nat.Prime n := by
  intro n hn
  unfold natSetOfState at hn
  rcases Finset.mem_map.mp hn with ⟨p, _hp, rfl⟩
  exact P.prime_mem p.1 p.property

/-- The product defining `stateNat` is the product over the underlying nat set. -/
def stateNat {P : PrimeCutoff} (S : SquareFreeState P) : ℕ :=
  ∏ n ∈ natSetOfState S, n

/-- The cardinality of the underlying nat set is the fermion number. -/
theorem card_natSetOfState
    {P : PrimeCutoff}
    (S : SquareFreeState P) :
    (natSetOfState S).card = S.card := by
  unfold natSetOfState
  exact Finset.card_map (primeModeEmbedding P)

/--
The Möbius value of the represented square-free integer is exactly the
fermion parity of the finite exterior state.
-/
theorem mobius_stateNat_eq_fermionParitySign
    {P : PrimeCutoff}
    (S : SquareFreeState P) :
    ArithmeticFunction.moebius (stateNat S) =
      SquareFreePrimeState.fermionParitySign S := by
  have hprime : ∀ n ∈ natSetOfState S, Nat.Prime n :=
    natSetOfState_prime_mem S
  simpa [stateNat, SquareFreePrimeState.fermionParitySign, card_natSetOfState] using
    (PrimeBitWittenIndex.mobius_prime_product_eq_parity (natSetOfState S) hprime)

/-- The global chirality is the Möbius readout of the represented integer. -/
theorem mobius_stateNat_eq_Gamma
    {P : PrimeCutoff}
    (S : SquareFreeState P) :
    ArithmeticFunction.moebius (stateNat S) = SquareFreePrimeState.Gamma S := by
  simp [SquareFreePrimeState.Gamma, mobius_stateNat_eq_fermionParitySign]

end InfoGeometry.Arithmetic.PrimeExteriorMobiusBridge
