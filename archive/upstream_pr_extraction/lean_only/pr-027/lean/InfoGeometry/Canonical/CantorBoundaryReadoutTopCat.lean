import InfoGeometry.Canonical.CantorBoundaryCuntzShiftTopCat
import InfoGeometry.Canonical.CantorBoundaryReadoutRefinement
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
open InfoGeometry.Canonical.CantorBoundaryReadoutRefinement
open InfoGeometry.Canonical.CantorCylinderTopology
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

def prefixExtendTopCatHom {n : ℕ} (w : BitWord n) :
    TopCat.of CantorBoundary ⟶ TopCat.of CantorBoundary :=
  TopCat.ofHom
    { toFun := prefixExtend w
      continuous_toFun := continuous_prefixExtend w }

def finitePrefixAffineTopCatHom (n : ℕ) (w : BitWord n) :
    TopCat.of ℝ ⟶ TopCat.of ℝ :=
  TopCat.ofHom
    { toFun := fun x =>
        finitePrefixReadout (List.ofFn w) + (1 / 2 : ℝ) ^ n * x
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

@[simp] theorem prefixExtendTopCatHom_apply {n : ℕ} (w : BitWord n)
    (x : CantorBoundary) :
    prefixExtendTopCatHom w x = prefixExtend w x :=
  rfl

@[simp] theorem finitePrefixAffineTopCatHom_apply (n : ℕ) (w : BitWord n)
    (x : ℝ) :
    finitePrefixAffineTopCatHom n w x =
      finitePrefixReadout (List.ofFn w) + (1 / 2 : ℝ) ^ n * x :=
  rfl

theorem prefixExtendTopCatHom_extendSucc {n : ℕ} (w : BitWord n) (b : Bool) :
    prefixExtendTopCatHom (extendSucc n w b) =
      prefixTopCatHom b ≫ prefixExtendTopCatHom w := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro x
  change prefixExtend (extendSucc n w b) x =
    prefixExtend w (prefixBit b x)
  exact prefixExtend_extendSucc_eq_prefixBit n w b x

theorem prefixExtend_readoutTopCat_square {n : ℕ} (w : BitWord n) :
    prefixExtendTopCatHom w ≫ readoutTopCatHom =
      readoutTopCatHom ≫ finitePrefixAffineTopCatHom n w := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro x
  rw [TopCat.comp_app]
  change realBinaryReadout (prefixExtend w x) =
    finitePrefixReadout (List.ofFn w) + (1 / 2 : ℝ) ^ n *
      realBinaryReadout x
  exact realBinaryReadout_prefixExtend n w x

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
