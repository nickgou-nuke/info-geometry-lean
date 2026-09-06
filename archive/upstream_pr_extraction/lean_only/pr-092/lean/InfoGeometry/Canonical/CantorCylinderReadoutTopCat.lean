import InfoGeometry.Canonical.CantorBoundaryReadoutRefinement
import InfoGeometry.Canonical.CantorBoundaryReadoutTopCat
import Mathlib.Topology.Category.TopCat.Basic

/-!
# TopCat finite-cylinder readout

Finite prefix cylinders are already homeomorphic to the Cantor boundary.  This
owner exposes that homeomorphism and the readout restricted to the cylinder as
`TopCat` morphisms, with the exact finite-prefix affine readout law.
-/

noncomputable section

namespace InfoGeometry.Canonical.CantorCylinderReadoutTopCat

open CategoryTheory
open InfoGeometry.Canonical.UHFInductiveColimitBoundary
open InfoGeometry.Canonical.CantorCylinderTopology
open InfoGeometry.Canonical.StoneCantorMathlib
open InfoGeometry.Canonical.CantorBoundaryReadoutBounds
open InfoGeometry.Canonical.CantorBoundaryFiniteReadout
open InfoGeometry.Canonical.CantorBoundaryReadoutRefinement
open InfoGeometry.Canonical.CantorBoundaryReadoutTopCat

def prefixCylinderTopCatIso (n : ℕ) (w : BitWord n) :
    TopCat.of (ℕ → Bool) ≅ TopCat.of (prefixCylinder n w) where
  hom := TopCat.ofHom
    { toFun := prefixCylinderHomeomorph n w
      continuous_toFun := (prefixCylinderHomeomorph n w).continuous }
  inv := TopCat.ofHom
    { toFun := (prefixCylinderHomeomorph n w).symm
      continuous_toFun := (prefixCylinderHomeomorph n w).symm.continuous }
  hom_inv_id := by
    apply TopCat.hom_ext
    ext x
    rw [TopCat.comp_app, TopCat.id_app]
    simp [TopCat.ofHom]
  inv_hom_id := by
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro x
    rw [TopCat.comp_app, TopCat.id_app]
    change prefixCylinderHomeomorph n w
        ((prefixCylinderHomeomorph n w).symm x) = x
    exact (prefixCylinderHomeomorph n w).apply_symm_apply x

def prefixCylinderReadoutTopCatHom (n : ℕ) (w : BitWord n) :
    TopCat.of (prefixCylinder n w) ⟶ TopCat.of ℝ :=
  TopCat.ofHom
    { toFun := fun x => realBinaryReadout x.1
      continuous_toFun := continuous_realBinaryReadout.comp continuous_subtype_val }

def prefixCylinderAffineReadoutTopCatHom (n : ℕ) (w : BitWord n) :
    TopCat.of ℝ ⟶ TopCat.of ℝ :=
  TopCat.ofHom
    { toFun := fun x =>
        finitePrefixReadout (List.ofFn w) + (1 / 2 : ℝ) ^ n * x
      continuous_toFun := by fun_prop }

@[simp] theorem prefixCylinderReadoutTopCatHom_apply
    (n : ℕ) (w : BitWord n) (x : prefixCylinder n w) :
    prefixCylinderReadoutTopCatHom n w x = realBinaryReadout x.1 := rfl

@[simp] theorem prefixCylinderAffineReadoutTopCatHom_apply
    (n : ℕ) (w : BitWord n) (x : ℝ) :
    prefixCylinderAffineReadoutTopCatHom n w x =
      finitePrefixReadout (List.ofFn w) + (1 / 2 : ℝ) ^ n * x := rfl

theorem prefixCylinder_readout_square (n : ℕ) (w : BitWord n) :
    (prefixCylinderTopCatIso n w).hom ≫ prefixCylinderReadoutTopCatHom n w =
      readoutTopCatHom ≫ prefixCylinderAffineReadoutTopCatHom n w := by
  apply TopCat.hom_ext
  ext x
  rw [TopCat.comp_app, TopCat.comp_app]
  dsimp [prefixCylinderTopCatIso, prefixCylinderReadoutTopCatHom,
    prefixCylinderAffineReadoutTopCatHom, TopCat.ofHom]
  have hreadout :
      (ConcreteCategory.hom readoutTopCatHom) x = realBinaryReadout x := by
    simp [InfoGeometry.Canonical.CantorBoundaryReadoutTopCat.readoutTopCatHom,
      TopCat.ofHom]
  rw [hreadout]
  change realBinaryReadout ((prefixCylinderHomeomorph n w x).1) =
    finitePrefixReadout (List.ofFn w) +
      (1 / 2 : ℝ) ^ n * realBinaryReadout x
  rw [prefixCylinderHomeomorph_apply]
  exact realBinaryReadout_prefixExtend n w x

theorem prefixCylinder_readout_interval (n : ℕ) (w : BitWord n) (x : (ℕ → Bool)) :
    realBinaryReadout (prefixExtend w x) ∈
      Set.Icc (finitePrefixReadout (List.ofFn w))
        (finitePrefixReadout (List.ofFn w) + (1 / 2 : ℝ) ^ n) :=
  realBinaryReadout_prefixExtend_mem_dyadicInterval n w x

end InfoGeometry.Canonical.CantorCylinderReadoutTopCat
