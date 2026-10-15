import InfoGeometry.Lie.SplitOctonionEllNativeClosedFlow
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Algebra.Zorn.Incidence
import InfoGeometry.Lie.SplitOctonionErlangenInvariant

/-!
# Quadratic isometry of the native split-octonion ell flow

The closed flow of `T = (1/2) ad_lUnit` preserves the actual canonical Zorn
determinant and its polarization.  This is a linear quadratic-isometry result;
it does not claim preservation of the nonassociative multiplication or
membership in the split `G₂` automorphism group.

The existing six-coordinate Klein owner uses the distinct diagonal axial
support.  Transport from this native mixed-coordinate support therefore awaits
an explicit intertwiner and is intentionally not asserted here.
-/

noncomputable section

namespace InfoGeometry.Lie.SplitOctonionEllNativeQuadraticIsometry

open InfoGeometry.Algebra.Zorn
open InfoGeometry.Algebra.Zorn.G2TrifactorSU3
open InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge
open InfoGeometry.Algebra.Zorn.SplitQuaternionCore
open InfoGeometry.Lie.SplitOctonionErlangenInvariant
open InfoGeometry.Lie.SplitOctonionEllNativeClosedFlow
open InfoGeometry.Lie.SplitOctonionEllNativeTrifactor
open InfoGeometry.Lie.SplitOctonionEllOperatorTrifactor
open InfoGeometry.Lie.SplitOctonionEllPolarization

abbrev CZ := CanonicalZorn

/-- The native closed flow bundled with its already proved inverse at `-t`. -/
def ellNativeFlowLinearEquiv (t : ℝ) : CZ ≃ₗ[ℝ] CZ where
  toLinearMap := ellNativeFlow t
  invFun := ellNativeFlow (-t)
  left_inv X := by
    have h := congrArg (fun F : Module.End ℝ CZ => F X)
      (ellNativeFlow_neg_mul t)
    simpa [Module.End.mul_apply] using h
  right_inv X := by
    have h := congrArg (fun F : Module.End ℝ CZ => F X)
      (ellNativeFlow_mul_neg t)
    simpa [Module.End.mul_apply] using h

@[simp] theorem ellNativeFlowLinearEquiv_apply (t : ℝ) (X : CZ) :
    ellNativeFlowLinearEquiv t X = ellNativeFlow t X :=
  rfl

@[simp] theorem coordAddEquiv_apply (z : CZ) :
    InfoGeometry.Canonical.ZornMatrix.coordAddEquiv z = (z.a, z.b, z.x, z.y) := rfl

@[simp] theorem coordAddEquiv_symm_apply (c : InfoGeometry.Canonical.ZornMatrix.Coord ℝ) :
    InfoGeometry.Canonical.ZornMatrix.coordAddEquiv.symm c = { a := c.1, b := c.2.1, x := c.2.2.1, y := c.2.2.2 } := rfl

@[simp] theorem coordAddEquiv_symm_a (c : InfoGeometry.Canonical.ZornMatrix.Coord ℝ) :
    (InfoGeometry.Canonical.ZornMatrix.coordAddEquiv.symm c).a = c.1 := rfl

@[simp] theorem coordAddEquiv_symm_b (c : InfoGeometry.Canonical.ZornMatrix.Coord ℝ) :
    (InfoGeometry.Canonical.ZornMatrix.coordAddEquiv.symm c).b = c.2.1 := rfl

@[simp] theorem coordAddEquiv_symm_x (c : InfoGeometry.Canonical.ZornMatrix.Coord ℝ) :
    (InfoGeometry.Canonical.ZornMatrix.coordAddEquiv.symm c).x = c.2.2.1 := rfl

@[simp] theorem coordAddEquiv_symm_y (c : InfoGeometry.Canonical.ZornMatrix.Coord ℝ) :
    (InfoGeometry.Canonical.ZornMatrix.coordAddEquiv.symm c).y = c.2.2.2 := rfl

@[simp] theorem coordEquiv_symm_a (c : InfoGeometry.Canonical.ZornMatrix.Coord ℝ) :
    (InfoGeometry.Canonical.ZornMatrix.coordEquiv.symm c).a = c.1 := rfl

@[simp] theorem coordEquiv_symm_b (c : InfoGeometry.Canonical.ZornMatrix.Coord ℝ) :
    (InfoGeometry.Canonical.ZornMatrix.coordEquiv.symm c).b = c.2.1 := rfl

@[simp] theorem coordEquiv_symm_x (c : InfoGeometry.Canonical.ZornMatrix.Coord ℝ) :
    (InfoGeometry.Canonical.ZornMatrix.coordEquiv.symm c).x = c.2.2.1 := rfl

@[simp] theorem coordEquiv_symm_y (c : InfoGeometry.Canonical.ZornMatrix.Coord ℝ) :
    (InfoGeometry.Canonical.ZornMatrix.coordEquiv.symm c).y = c.2.2.2 := rfl

@[simp] theorem sub_a (z1 z2 : CZ) : (z1 - z2).a = z1.a - z2.a := rfl
@[simp] theorem sub_b (z1 z2 : CZ) : (z1 - z2).b = z1.b - z2.b := rfl
@[simp] theorem sub_x (z1 z2 : CZ) : (z1 - z2).x = z1.x - z2.x := rfl
@[simp] theorem sub_y (z1 z2 : CZ) : (z1 - z2).y = z1.y - z2.y := rfl

@[simp] theorem neg_a (z : CZ) : (-z).a = -z.a := rfl
@[simp] theorem neg_b (z : CZ) : (-z).b = -z.b := rfl
@[simp] theorem neg_x (z : CZ) : (-z).x = -z.x := rfl
@[simp] theorem neg_y (z : CZ) : (-z).y = -z.y := rfl

set_option maxHeartbeats 1600000

/-- The native closed ell flow preserves the full `(4,4)` Zorn quadratic
form.  The proof expands the actual mixed-coordinate `lUnit` action rather
than replacing it by the distinct diagonal axial flow. -/
theorem detZ_ellNativeFlow (t : ℝ) (Z : CZ) :
    ZornMatrix.detZ realCrossProduct3 (ellNativeFlow t Z) =
      ZornMatrix.detZ realCrossProduct3 Z := by
  unfold realCrossProduct3
  simp [ellNativeFlow, flowZero, flowPlus, flowMinus, ellGrading,
    ellCommutator, lUnit, zMul, ZornMatrix.detZ,
    InfoGeometry.Canonical.ZornMatrix.dot,
    InfoGeometry.Canonical.ZornMatrix.cross,
    Equiv.smul_def,
    InfoGeometry.Canonical.ZornMatrix.coordAddEquiv,
    InfoGeometry.Canonical.ZornMatrix.coordEquiv]
  rw [Real.exp_neg]
  field_simp [Real.exp_ne_zero]
  ring

@[simp] theorem detZ_ellNativeFlowLinearEquiv (t : ℝ) (Z : CZ) :
    ZornMatrix.detZ realCrossProduct3 (ellNativeFlowLinearEquiv t Z) =
      ZornMatrix.detZ realCrossProduct3 Z :=
  detZ_ellNativeFlow t Z

/-- The native closed flow as a Mathlib quadratic isometry. -/
def ellNativeFlowQuadraticIsometry (t : ℝ) :
    canonicalDetQuadratic.IsometryEquiv canonicalDetQuadratic :=
  { ellNativeFlowLinearEquiv t with
    map_app' := fun Z => by
      simpa [canonicalDetQuadratic] using detZ_ellNativeFlowLinearEquiv t Z }

@[simp] theorem ellNativeFlowQuadraticIsometry_apply (t : ℝ) (Z : CZ) :
    ellNativeFlowQuadraticIsometry t Z = ellNativeFlow t Z :=
  rfl

@[simp] theorem ellNativeFlowQuadraticIsometry_preserves_form
    (t : ℝ) (Z : CZ) :
    canonicalDetQuadratic (ellNativeFlowQuadraticIsometry t Z) =
      canonicalDetQuadratic Z :=
  QuadraticMap.IsometryEquiv.map_app (ellNativeFlowQuadraticIsometry t) Z

/-- Polarization of the Zorn determinant is invariant under the same flow. -/
theorem polarZ_ellNativeFlow (t : ℝ) (X Y : CZ) :
    polarZ realCrossProduct3 (ellNativeFlow t X) (ellNativeFlow t Y) =
      polarZ realCrossProduct3 X Y := by
  unfold polarZ
  rw [← map_add, detZ_ellNativeFlow, detZ_ellNativeFlow,
    detZ_ellNativeFlow]

/-- The representative-level Zorn null cone is invariant in both
directions under the native flow. -/
theorem detZ_ellNativeFlow_eq_zero_iff (t : ℝ) (Z : CZ) :
    ZornMatrix.detZ realCrossProduct3 (ellNativeFlow t Z) = 0 ↔
      ZornMatrix.detZ realCrossProduct3 Z = 0 := by
  rw [detZ_ellNativeFlow]

end InfoGeometry.Lie.SplitOctonionEllNativeQuadraticIsometry
