import InfoGeometry.Lie.SplitOctonionEllCircularOperatorCoordinates
import InfoGeometry.Lie.SplitOctonionErlangenInvariant
import InfoGeometry.Lie.SplitOctonionCircularReciprocalExponentialBridge

/-!
# The native determinant in circular Peirce coordinates

The circular coordinates carry the native Zorn determinant by a genuine
`QuadraticForm.comp` transport.  No coordinate polynomial or associativity
claim is imposed; the transported form is definitionally the determinant of
the canonical alternative carrier.
-/

noncomputable section

namespace InfoGeometry.Lie.SplitOctonionEllCircularQuadraticCoordinates

open InfoGeometry.Lie.SplitOctonionEllCircularOperatorCoordinates
open InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis
open InfoGeometry.Lie.SplitOctonionEllCircularAxialGrading
open InfoGeometry.Lie.SplitOctonionEllCrossChannel
open InfoGeometry.Lie.SplitOctonionEllPolarization
open InfoGeometry.Lie.SplitOctonionErlangenInvariant
open InfoGeometry.Lie.SplitOctonionCircularReciprocalExponentialBridge
open InfoGeometry.Algebra.Zorn.SplitQuaternionCore
open InfoGeometry.Algebra.Zorn.SplitOctonionWittPlanes
open InfoGeometry.Canonical.ZornMatrix

abbrev CanonicalZorn :=
  InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis.CanonicalZorn

noncomputable def circularPeirceQuadratic :
    QuadraticForm ℝ (Fin 8 → ℝ) :=
  canonicalDetQuadratic.comp circularPeirceBasis.equivFun.symm

theorem circularPeirceQuadratic_apply_coord (x : Fin 8 → ℝ) :
    circularPeirceQuadratic x =
      canonicalDetQuadratic (circularPeirceBasis.equivFun.symm x) := by
  rfl

set_option maxHeartbeats 1000000
theorem circularPeirceQuadratic_formula (x : Fin 8 → ℝ) :
    circularPeirceQuadratic x =
      x 0 * x 4 - (x 1 * x 5 + x 2 * x 6 + x 3 * x 7) := by
  rw [circularPeirceQuadratic_apply_coord]
  rw [circularPeirceBasis.equivFun_symm_apply]
  change InfoGeometry.Algebra.Zorn.ZornMatrix.detZ
    (∑ i : Fin 8, x i • circularPeirceBasis i) = _
  rw [show (∑ i : Fin 8, x i • circularPeirceBasis i) =
      ∑ i : Fin 8, x i • frame i by
    apply Finset.sum_congr rfl
    intro i hi
    rw [circularPeirceBasis_apply]]
  have hsmul (r : ℝ) (Z : CanonicalZorn) :
      r • Z = { a := r * Z.a, b := r * Z.b, x := r • Z.x, y := r • Z.y } := by
    rw [Equiv.smul_def InfoGeometry.Canonical.ZornMatrix.coordEquiv]
    rfl
  rw [Fin.sum_univ_eight]
  simp only [frame, uPlus, uMinus, rootPlus, rootMinus,
    chiralNull, ellBasis, quaternionBasis, iUnit, jUnit, kQuaternionUnit,
    lUnit, InfoGeometry.Algebra.Zorn.ZornMatrix.detZ,
    hsmul]
  simp [InfoGeometry.Algebra.Zorn.G2TrifactorSU3.zMul,
    InfoGeometry.Canonical.ZornMatrix.dot,
    InfoGeometry.Canonical.ZornMatrix.cross]
  ring

theorem circularPeirceQuadratic_zero_iff (x : Fin 8 → ℝ) :
    circularPeirceQuadratic x = 0 ↔
      x 0 * x 4 = x 1 * x 5 + x 2 * x 6 + x 3 * x 7 := by
  rw [circularPeirceQuadratic_formula]
  constructor <;> intro h <;> linarith

@[simp] theorem circularPeirceQuadratic_apply (X : CanonicalZorn) :
    circularPeirceQuadratic (coordinateEquiv X) =
      InfoGeometry.Algebra.Zorn.ZornMatrix.detZ X := by
  change canonicalDetQuadratic
      (circularPeirceBasis.equivFun.symm (coordinateEquiv X)) = _
  change canonicalDetQuadratic
      (circularPeirceBasis.equivFun.symm
        (circularPeirceBasis.equivFun X)) = _
  rw [circularPeirceBasis.equivFun.symm_apply_apply]
  simp [canonicalDetQuadratic]

theorem circularPeirceQuadratic_null_iff (X : CanonicalZorn) :
    circularPeirceQuadratic (coordinateEquiv X) = 0 ↔
      InfoGeometry.Algebra.Zorn.ZornMatrix.detZ X = 0 := by
  rw [circularPeirceQuadratic_apply]

theorem detZ_null_iff_circularPeirceQuadratic_null (X : CanonicalZorn) :
    InfoGeometry.Algebra.Zorn.ZornMatrix.detZ X = 0 ↔
      circularPeirceQuadratic (coordinateEquiv X) = 0 := by
  rw [circularPeirceQuadratic_apply]

theorem detZ_coordinate_zero_iff (X : CanonicalZorn) :
    InfoGeometry.Algebra.Zorn.ZornMatrix.detZ X = 0 ↔
      coordinateEquiv X 0 * coordinateEquiv X 4 =
        coordinateEquiv X 1 * coordinateEquiv X 5 +
          coordinateEquiv X 2 * coordinateEquiv X 6 +
          coordinateEquiv X 3 * coordinateEquiv X 7 := by
  rw [← circularPeirceQuadratic_apply X,
    circularPeirceQuadratic_zero_iff]

theorem circularPeirceQuadratic_axialFlowCoordinate (t : ℝ) (x : Fin 8 → ℝ) :
    circularPeirceQuadratic (axialFlowCoordinate t x) =
      circularPeirceQuadratic x := by
  rw [circularPeirceQuadratic_formula, circularPeirceQuadratic_formula]
  dsimp [axialFlowCoordinate]
  simp only [axialWeight, mul_zero, Real.exp_zero, one_mul, mul_one,
    mul_neg]
  rw [reciprocal_exponential_channel_invariant,
    reciprocal_exponential_channel_invariant,
    reciprocal_exponential_channel_invariant]

theorem circularPeirceQuadratic_axialFlowCoordinate_zero_iff
    (t : ℝ) (x : Fin 8 → ℝ) :
    circularPeirceQuadratic (axialFlowCoordinate t x) = 0 ↔
      circularPeirceQuadratic x = 0 := by
  rw [circularPeirceQuadratic_axialFlowCoordinate]

theorem circularPeirceQuadratic_axialFlow_zero_iff
    (t : ℝ) (X : CanonicalZorn) :
    circularPeirceQuadratic (coordinateEquiv (axialFlow t X)) = 0 ↔
      circularPeirceQuadratic (coordinateEquiv X) = 0 := by
  have hcoord : coordinateEquiv (axialFlow t X) =
      axialFlowCoordinate t (coordinateEquiv X) := by
    funext i
    exact coordinateEquiv_axialFlow_apply t X i
  rw [hcoord, circularPeirceQuadratic_axialFlowCoordinate]

noncomputable def circularPeirceQuadraticIsometry :
    canonicalDetQuadratic.IsometryEquiv circularPeirceQuadratic :=
  QuadraticMap.IsometryEquiv.mk circularPeirceBasis.equivFun (by
    intro X
    change circularPeirceQuadratic (coordinateEquiv X) =
      InfoGeometry.Algebra.Zorn.ZornMatrix.detZ X
    exact circularPeirceQuadratic_apply X)

@[simp] theorem circularPeirceQuadraticIsometry_map_app (X : CanonicalZorn) :
    circularPeirceQuadratic (circularPeirceQuadraticIsometry X) =
      canonicalDetQuadratic X :=
  circularPeirceQuadraticIsometry.map_app X

@[simp] theorem circularPeirceQuadraticIsometry_symm_map_app
    (x : Fin 8 → ℝ) :
    canonicalDetQuadratic (circularPeirceQuadraticIsometry.symm x) =
      circularPeirceQuadratic x :=
  circularPeirceQuadraticIsometry.symm.map_app x

end InfoGeometry.Lie.SplitOctonionEllCircularQuadraticCoordinates
