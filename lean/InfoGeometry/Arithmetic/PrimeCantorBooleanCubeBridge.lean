import Mathlib.Tactic
import InfoGeometry.Meta.BridgeTarget
import InfoGeometry.Arithmetic.PrimeBooleanCube
import InfoGeometry.Arithmetic.PrimeCantorLatticeDirac

/-!
# InfoGeometry.Arithmetic.PrimeCantorBooleanCubeBridge

Thin bridge from the Cantor-lattice Dirac carrier to the canonical finite
Boolean-cube owner.

This file does not introduce new arithmetic content. It simply re-exports the
canonical chirality/Möbius readbacks in the Cantor-lattice naming surface so
the older carrier can delegate cleanly.
-/

noncomputable section

namespace InfoGeometry.Arithmetic.PrimeCantorBooleanCubeBridge

open InfoGeometry.Arithmetic.PrimeBooleanCube
open InfoGeometry.Arithmetic.PrimeCantorLatticeDirac
open InfoGeometry.Arithmetic.PrimeBitWittenIndex

/-- Cantor-lattice chirality readback delegates to the canonical Boolean cube. -/
@[bridge_target_tag]
theorem globalMajoranaChirality_eq_neg_one_pow_card_canonical
    (P : InfoGeometry.Arithmetic.PrimeBitWittenIndex.PrimeRegister)
    (S : Finset ℕ) (hS : S ⊆ P.primes) :
    PrimeCantorLatticeDirac.globalMajoranaChirality P S = (-1 : ℤ) ^ S.card := by
  simpa [PrimeCantorLatticeDirac.globalMajoranaChirality,
    PrimeCantorLatticeDirac.localMajoranaParity,
    PrimeCantorLatticeDirac.occupationInt,
    PrimeBooleanCube.globalChirality,
    PrimeBooleanCube.localParity,
    PrimeBooleanCube.occupationInt] using
      (PrimeBooleanCube.globalChirality_eq_neg_one_pow_card P hS)

/-- Cantor-lattice Möbius readback delegates to the canonical Boolean cube. -/
@[bridge_target_tag]
theorem mobius_representedNat_eq_fermionParity_canonical
    (P : InfoGeometry.Arithmetic.PrimeBitWittenIndex.PrimeRegister)
    (v : PrimeCantorLatticeDirac.CantorVertex P) :
    ArithmeticFunction.moebius (PrimeCantorLatticeDirac.vertexNat P v) =
      PrimeBooleanCube.fermionParity v := by
  simpa [PrimeCantorLatticeDirac.vertexNat,
    PrimeBooleanCube.representedNat,
    PrimeBooleanCube.fermionParity] using
      (PrimeBooleanCube.mobius_representedNat_eq_fermionParity P v)

end InfoGeometry.Arithmetic.PrimeCantorBooleanCubeBridge
