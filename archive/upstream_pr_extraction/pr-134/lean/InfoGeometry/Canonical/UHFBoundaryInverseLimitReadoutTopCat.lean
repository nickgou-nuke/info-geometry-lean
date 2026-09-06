import InfoGeometry.Canonical.UHFInductiveColimitBoundaryInverseLimit
import InfoGeometry.Canonical.CantorBoundaryReadoutTopCat

/-!
# Binary readout on the categorical prefix inverse limit

The Cantor boundary is already identified with the `TopCat` limit of its
finite prefix diagram.  This owner transports the continuous binary readout
and its affine branch recursion across that canonical isomorphism.
-/

noncomputable section

namespace InfoGeometry.Canonical.UHFBoundaryInverseLimitReadoutTopCat

open CategoryTheory CategoryTheory.Limits
open InfoGeometry.Canonical.UHFInductiveColimitBoundary
open InfoGeometry.Canonical.UHFInductiveColimitBoundaryInverseLimit
open InfoGeometry.Canonical.CuntzCantorBoundaryShift
open InfoGeometry.Canonical.CantorBoundaryReadoutTopCat
open InfoGeometry.Canonical.CantorBoundaryReadoutBounds
open InfoGeometry.Canonical.CantorBoundaryCuntzShift

def inverseLimitReadoutTopCatHom :
    TopCat.of (↑(limit prefixDiagram)) ⟶ TopCat.of ℝ :=
  prefixBoundaryLimitIso.inv ≫ readoutTopCatHom

@[simp] theorem inverseLimitReadoutTopCatHom_apply
    (x : ↑(limit prefixDiagram)) :
    inverseLimitReadoutTopCatHom x =
      realBinaryReadout (prefixBoundaryLimitIso.inv x) :=
  rfl

theorem inverseLimitReadout_prefixLimitPrependBit_square (b : Bool) :
    prefixLimitPrependBit b ≫ inverseLimitReadoutTopCatHom =
      inverseLimitReadoutTopCatHom ≫ branchAffineTopCatHom b := by
  dsimp [prefixLimitPrependBit, inverseLimitReadoutTopCatHom]
  simp only [Category.assoc]
  rw [← Category.assoc prefixBoundaryLimitIso.hom
    prefixBoundaryLimitIso.inv readoutTopCatHom]
  rw [prefixBoundaryLimitIso.hom_inv_id]
  have hprepend : prependBit b = prefixBit b := by
    funext x n
    cases n with
    | zero => simp [prependBit, prefixBit]
    | succ n => simp [prependBit, prefixBit]
  simpa [prependBitHom, prefixTopCatHom, hprepend, Category.comp_id] using
    congrArg (fun f => prefixBoundaryLimitIso.inv ≫ f)
      (readout_prefixTopCat_square b)

theorem inverseLimitReadout_leftShift_square :
    prefixLimitPrependBit false ≫ inverseLimitReadoutTopCatHom =
      inverseLimitReadoutTopCatHom ≫ branchAffineTopCatHom false :=
  inverseLimitReadout_prefixLimitPrependBit_square false

theorem inverseLimitReadout_rightShift_square :
    prefixLimitPrependBit true ≫ inverseLimitReadoutTopCatHom =
      inverseLimitReadoutTopCatHom ≫ branchAffineTopCatHom true :=
  inverseLimitReadout_prefixLimitPrependBit_square true

end InfoGeometry.Canonical.UHFBoundaryInverseLimitReadoutTopCat
