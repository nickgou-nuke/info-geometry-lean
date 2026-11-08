import InfoGeometry.Canonical.CantorProjectiveLimitBranchTopCat
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.CantorProjectiveLimitReadoutTopCat
import InfoGeometry.Canonical.CantorBoundaryReadoutTopCat

/-!
# Branch/readout recursion on the concrete projective limit

The binary affine recursion is transported from the Cantor boundary to the
coherent-prefix projective-limit carrier.
-/

noncomputable section

namespace InfoGeometry.Canonical.CantorProjectiveLimitBranchReadoutTopCat

open CategoryTheory
open InfoGeometry.Canonical.UHFInductiveColimitBoundary
open InfoGeometry.Canonical.CuntzCantorBoundaryShift
open InfoGeometry.Canonical.CantorBoundaryCuntzShift
open InfoGeometry.Canonical.CantorBoundaryReadoutBounds
open InfoGeometry.Canonical.CantorBoundaryReadoutTopCat
open InfoGeometry.Canonical.CantorProjectiveLimit
open InfoGeometry.Canonical.CantorProjectiveLimit.PrefixProjectiveLimit
open InfoGeometry.Canonical.CantorProjectiveLimitBranchTopCat
open InfoGeometry.Canonical.CantorProjectiveLimitReadoutTopCat

theorem projective_branch_readout_square (b : Bool) :
    projectivePrependBitTopCatHom b ≫ projectiveLimitReadoutTopCatHom =
      projectiveLimitReadoutTopCatHom ≫ branchAffineTopCatHom b := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro p
  rw [TopCat.comp_app, TopCat.comp_app]
  change realBinaryReadout
      (toCantor (projectivePrependBitTopCatHom b p)) =
    (if b then (1 / 2 : ℝ) else 0) +
      (1 / 2 : ℝ) * realBinaryReadout (toCantor p)
  rw [projectivePrependBitTopCatHom_apply]
  change realBinaryReadout
      (toCantor (ofCantor (prependBit b (toCantor p)))) =
    (if b then (1 / 2 : ℝ) else 0) +
      (1 / 2 : ℝ) * realBinaryReadout (toCantor p)
  rw [toCantor_ofCantor]
  have hprepend : prependBit b = prefixBit b := by
    funext x n
    cases n with
    | zero => simp [prependBit, prefixBit]
    | succ n => simp [prependBit, prefixBit]
  rw [hprepend]
  exact realBinaryReadout_prefixBit b (toCantor p)

end InfoGeometry.Canonical.CantorProjectiveLimitBranchReadoutTopCat
