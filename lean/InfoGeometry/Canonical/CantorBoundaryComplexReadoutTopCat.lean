import InfoGeometry.Canonical.CantorBoundaryReadoutComplexRealBridge
import InfoGeometry.Canonical.CantorBoundaryReadoutTopCat
import Mathlib.Topology.Category.TopCat.Basic

/-!
# TopCat readout for the complexified Cantor boundary

The complex binary readout is the `ofReal` image of the established real
readout.  This owner exposes that map and its branch recursion in `TopCat`.
-/

noncomputable section

namespace InfoGeometry.Canonical.CantorBoundaryComplexReadoutTopCat

open CategoryTheory
open InfoGeometry.Canonical.FractalCantorCliffordFockBridge
open InfoGeometry.Canonical.CantorBoundaryComplexReadout
open InfoGeometry.Canonical.CantorBoundaryReadoutComplexRealBridge
open InfoGeometry.Canonical.CantorBoundaryReadoutBounds
open InfoGeometry.Canonical.CantorBoundaryFiniteReadout
open InfoGeometry.Canonical.CantorBoundaryReadoutRefinement
open InfoGeometry.Canonical.CantorBoundaryReadoutTopCat
open InfoGeometry.Canonical.CantorBoundaryCuntzShift
open InfoGeometry.Canonical.CantorCylinderTopology

def complexBinaryReadoutTopCatHom :
    TopCat.of InfiniteBinaryWordSpace ⟶ TopCat.of ℂ :=
  TopCat.ofHom
    { toFun := binaryReadout
      continuous_toFun := by
        rw [show binaryReadout = fun w => (realBinaryReadout w : ℂ) by
          funext w
          exact complex_binaryReadout_eq_ofReal w]
        exact Complex.continuous_ofReal.comp continuous_realBinaryReadout }

def complexBranchAffineTopCatHom (b : Bool) :
    TopCat.of ℂ ⟶ TopCat.of ℂ :=
  TopCat.ofHom
    { toFun := fun z =>
        (if b then (1 / 2 : ℂ) else 0) + (1 / 2 : ℂ) * z
      continuous_toFun := by
        cases b <;> fun_prop }

def complexOfRealTopCatHom :
    TopCat.of ℝ ⟶ TopCat.of ℂ :=
  TopCat.ofHom
    { toFun := Complex.ofReal
      continuous_toFun := Complex.continuous_ofReal }

@[simp] theorem complexBinaryReadoutTopCatHom_apply
    (w : InfiniteBinaryWordSpace) :
    complexBinaryReadoutTopCatHom w = binaryReadout w := rfl

@[simp] theorem complexBranchAffineTopCatHom_apply
    (b : Bool) (z : ℂ) :
    complexBranchAffineTopCatHom b z =
      (if b then (1 / 2 : ℂ) else 0) + (1 / 2 : ℂ) * z := rfl

theorem complexBinaryReadoutTopCatHom_factorization :
    complexBinaryReadoutTopCatHom =
      readoutTopCatHom ≫ complexOfRealTopCatHom := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro w
  rw [TopCat.comp_app]
  change binaryReadout w = Complex.ofReal (realBinaryReadout w)
  exact complex_binaryReadout_eq_ofReal w

theorem complex_binaryReadout_prefixExtend
    (n : ℕ) (w : InfoGeometry.Canonical.UHFInductiveColimitBoundary.BitWord n)
    (x : InfiniteBinaryWordSpace) :
    binaryReadout (prefixExtend w x) =
      (finitePrefixReadout (List.ofFn w) : ℂ) +
        (1 / 2 : ℂ) ^ n * binaryReadout x := by
  rw [complex_binaryReadout_eq_ofReal,
    complex_binaryReadout_eq_ofReal]
  have h := congrArg Complex.ofReal
    (realBinaryReadout_prefixExtend n w x)
  simpa [Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_pow] using h

theorem complexBinaryReadout_prefixTopCat_square (b : Bool) :
    prefixTopCatHom b ≫ complexBinaryReadoutTopCatHom =
      complexBinaryReadoutTopCatHom ≫ complexBranchAffineTopCatHom b := by
  ext w
  change binaryReadout (prefixBit b w) =
    (if b then (1 / 2 : ℂ) else 0) + (1 / 2 : ℂ) * binaryReadout w
  rw [complex_binaryReadout_eq_ofReal, complex_binaryReadout_eq_ofReal]
  cases b with
  | false =>
      simpa using congrArg Complex.ofReal (realBinaryReadout_prefixBit false w)
  | true =>
      simpa using congrArg Complex.ofReal (realBinaryReadout_prefixBit true w)

theorem complexBinaryReadout_leftShift_square :
    prefixTopCatHom false ≫ complexBinaryReadoutTopCatHom =
      complexBinaryReadoutTopCatHom ≫ complexBranchAffineTopCatHom false :=
  complexBinaryReadout_prefixTopCat_square false

theorem complexBinaryReadout_rightShift_square :
    prefixTopCatHom true ≫ complexBinaryReadoutTopCatHom =
      complexBinaryReadoutTopCatHom ≫ complexBranchAffineTopCatHom true :=
  complexBinaryReadout_prefixTopCat_square true

end InfoGeometry.Canonical.CantorBoundaryComplexReadoutTopCat
