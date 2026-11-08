import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Meta.BridgeTarget
import InfoGeometry.Arithmetic.PrimeBooleanCube
import InfoGeometry.Arithmetic.PrimeCantorBooleanCubeBridge
import InfoGeometry.Arithmetic.PrimeCantorLatticeDirac

/-!
# InfoGeometry.Arithmetic.PrimeCantorLatticeDiracBridge

Bridge-only aliases for the finite Cantor-lattice Dirac naming surface.

This file does not add new arithmetic content. It reuses the canonical Boolean
cube and exterior carriers for the finite chirality and Möbius readouts, and it
keeps the Cantor-lattice Witten/Pfaffian readout as a bridge target.

No infinite Euler product.
No analytic continuation.
No Hilbert--Polya claim.
-/

noncomputable section

open scoped BigOperators
open scoped ArithmeticFunction.Moebius

namespace InfoGeometry.Arithmetic.PrimeCantorLatticeDiracBridge

open InfoGeometry.Arithmetic.PrimeBooleanCube
open InfoGeometry.Arithmetic.PrimeCantorBooleanCubeBridge
open InfoGeometry.Arithmetic.PrimeCantorLatticeDirac

/-- Cantor-lattice chirality delegates to the canonical Boolean cube. -/
@[bridge_target_tag]
theorem globalMajoranaChirality_eq_neg_one_pow_card_bridge
    (P : InfoGeometry.Arithmetic.PrimeBitWittenIndex.PrimeRegister)
    (S : Finset ℕ) (hS : S ⊆ P.primes) :
    InfoGeometry.Arithmetic.PrimeCantorLatticeDirac.globalMajoranaChirality P S =
      (-1 : ℤ) ^ S.card := by
  simpa [InfoGeometry.Arithmetic.PrimeCantorLatticeDirac.globalMajoranaChirality,
    InfoGeometry.Arithmetic.PrimeCantorLatticeDirac.localMajoranaParity,
    InfoGeometry.Arithmetic.PrimeCantorLatticeDirac.occupationInt] using
      (globalMajoranaChirality_eq_neg_one_pow_card_canonical (P := P) (S := S) hS)

/-- Cantor-lattice Möbius readout delegates to the canonical Boolean cube. -/
@[bridge_target_tag]
theorem mobius_representedNat_eq_fermionParity_bridge
    (P : InfoGeometry.Arithmetic.PrimeBitWittenIndex.PrimeRegister)
    (v : InfoGeometry.Arithmetic.PrimeCantorLatticeDirac.CantorVertex P) :
    ArithmeticFunction.moebius (InfoGeometry.Arithmetic.PrimeCantorLatticeDirac.vertexNat P v) =
      PrimeBooleanCube.fermionParity v := by
  simpa [InfoGeometry.Arithmetic.PrimeCantorLatticeDirac.vertexNat,
    PrimeBooleanCube.representedNat,
    PrimeBooleanCube.fermionParity] using
      (mobius_representedNat_eq_fermionParity_canonical (P := P) (v := v))

/--
Cantor-lattice Dirac Witten character bridge target.

This keeps the finite Dirac/Witten/Pfaffian naming surface visible while
delegating the actual finite Euler-product proof to the existing owner.
-/
@[bridge_target_tag]
theorem cantorDiracWittenCharacter_eq_eulerProduct_bridge
    (P : InfoGeometry.Arithmetic.PrimeBitWittenIndex.PrimeRegister)
    (q : ℕ → ℝ) :
    InfoGeometry.Arithmetic.PrimeCantorLatticeDirac.cantorDiracWittenCharacter P q =
      ∏ p ∈ P.primes, (1 - q p) := by
  exact InfoGeometry.Arithmetic.PrimeCantorLatticeDirac.cantorDiracWittenCharacter_eq_eulerProduct P q

end InfoGeometry.Arithmetic.PrimeCantorLatticeDiracBridge
