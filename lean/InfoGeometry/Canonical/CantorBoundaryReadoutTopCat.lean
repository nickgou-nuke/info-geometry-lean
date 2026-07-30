import InfoGeometry.Canonical.CantorBoundaryCuntzShiftTopCat
import Mathlib.Topology.Category.TopCat.Basic

/-!
# `TopCat` readout square for the symbolic Cantor branches

The binary readout is continuous and satisfies an affine recursion on each
prefix branch.  This owner records that recursion as an equality of
categorical continuous maps.
-/

noncomputable section

namespace InfoGeometry.Canonical.CantorBoundaryReadoutTopCat

open CategoryTheory CategoryTheory.Limits
open InfoGeometry.Canonical.CantorBoundaryCuntzShift
open InfoGeometry.Canonical.CantorBoundaryFiniteReadout
open InfoGeometry.Canonical.CantorBoundaryReadoutBounds
open InfoGeometry.Canonical.UHFInductiveColimitBoundary

def readoutTopCatHom :
    TopCat.of CantorBoundary ⟶ TopCat.of ℝ :=
  TopCat.ofHom
    { toFun := realBinaryReadout
      continuous_toFun := continuous_realBinaryReadout }

def prefixTopCatHom (b : Bool) :
    TopCat.of CantorBoundary ⟶ TopCat.of CantorBoundary :=
  TopCat.ofHom
    { toFun := prefixBit b
      continuous_toFun := continuous_prefixBit b }

def branchAffineTopCatHom (b : Bool) :
    TopCat.of ℝ ⟶ TopCat.of ℝ :=
  TopCat.ofHom
    { toFun := fun x => (if b then (1 / 2 : ℝ) else 0) + (1 / 2 : ℝ) * x
      continuous_toFun := by fun_prop }

@[simp] theorem readoutTopCatHom_apply (x : CantorBoundary) :
    readoutTopCatHom x = realBinaryReadout x :=
  rfl

@[simp] theorem prefixTopCatHom_apply (b : Bool) (x : CantorBoundary) :
    prefixTopCatHom b x = prefixBit b x :=
  rfl

@[simp] theorem branchAffineTopCatHom_apply (b : Bool) (x : ℝ) :
    branchAffineTopCatHom b x =
      (if b then (1 / 2 : ℝ) else 0) + (1 / 2 : ℝ) * x :=
  rfl

theorem readout_prefixTopCat_square (b : Bool) :
    prefixTopCatHom b ≫ readoutTopCatHom =
      readoutTopCatHom ≫ branchAffineTopCatHom b := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro x
  change realBinaryReadout (prefixBit b x) =
    (if b then (1 / 2 : ℝ) else 0) +
      (1 / 2 : ℝ) * realBinaryReadout x
  exact realBinaryReadout_prefixBit b x

theorem readout_leftShift_square :
    prefixTopCatHom false ≫ readoutTopCatHom =
      readoutTopCatHom ≫ branchAffineTopCatHom false := by
  exact readout_prefixTopCat_square false

theorem readout_rightShift_square :
    prefixTopCatHom true ≫ readoutTopCatHom =
      readoutTopCatHom ≫ branchAffineTopCatHom true := by
  exact readout_prefixTopCat_square true

end InfoGeometry.Canonical.CantorBoundaryReadoutTopCat
