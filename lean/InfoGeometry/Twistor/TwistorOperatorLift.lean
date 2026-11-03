/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Twistor.TwistorZornDerivationTransport
import InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge
import InfoGeometry.Algebra.ZornLeftMultiplicationDefect

/-!
# Faithful operator lift of the Penrose twistor carrier

The established real-linear twistor-to-Zorn equivalence is followed by the
native Zorn left-regular action into `Module.End`. The lift is faithful and
linear. Its failure to preserve the transported twistor product is exactly
the already-owned Zorn associator defect; no associative matrix product is
imposed on the twistor carrier.
-/

noncomputable section

namespace InfoGeometry.Twistor.TwistorOperatorLift

open InfoGeometry.Twistor.PenroseIncidence
open InfoGeometry.Twistor.RealSplitOctonionCarrierBridge
open InfoGeometry.Twistor.ChiralTwistorPeirceSheets
open InfoGeometry.Twistor.TwistorZornDerivationTransport
open InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge
open InfoGeometry.Algebra.ZornLeftCAR

/-- The existing coordinate soldering, with its proved additive and scalar
compatibility exposed as a linear map. -/
def canonicalZornToVectorLinearMap : CanonicalZorn →ₗ[ℝ]
    InfoGeometry.Algebra.ZornVectorMatrix ℝ where
  toFun := canonicalVectorEquiv
  map_add' := canonicalVectorEquiv_add
  map_smul' := canonicalVectorEquiv_smul

/-- The established twistor-to-canonical-Zorn map followed by the repository's
canonical Zorn/vector-matrix equivalence. -/
def twistorZornLinearMap : Twistor4 →ₗ[ℝ] InfoGeometry.Algebra.ZornVectorMatrix ℝ :=
  canonicalZornToVectorLinearMap.comp twistorRealEquivZorn.toLinearMap

/-- The transported twistor multiplication agrees with the native Zorn
vector-matrix product after carrier transport. -/
theorem twistorZornLinearMap_mul (z w : Twistor4) :
    twistorZornLinearMap (twistorMul z w) =
      InfoGeometry.Algebra.ZornVectorMatrix.mul (twistorZornLinearMap z) (twistorZornLinearMap w) := by
  change canonicalVectorEquiv (twistorRealEquivZorn (twistorMul z w)) =
    InfoGeometry.Algebra.ZornVectorMatrix.mul
      (canonicalVectorEquiv (twistorRealEquivZorn z))
      (canonicalVectorEquiv (twistorRealEquivZorn w))
  rw [twistorRealEquivZorn_mul, canonicalVectorEquiv_mul]

/-- The operator representation of a realified Penrose twistor, using the
repository's existing Zorn carrier and left-regular action. -/
def twistorOperatorLift : Twistor4 →ₗ[ℝ]
    Module.End ℝ (InfoGeometry.Algebra.ZornVectorMatrix ℝ) :=
  leftMultiplication.comp twistorZornLinearMap

/-- The operator lift retains all twistor directions: left multiplication is
faithful on the Zorn carrier, and the twistor-to-Zorn map is an equivalence. -/
theorem twistorOperatorLift_injective : Function.Injective twistorOperatorLift := by
  intro z w h
  have hLift : leftMultiplication (twistorZornLinearMap z) =
      leftMultiplication (twistorZornLinearMap w) := by
    change leftMultiplication (twistorZornLinearMap z) =
      leftMultiplication (twistorZornLinearMap w) at h
    exact h
  have hZorn := leftMultiplication_injective hLift
  apply twistorRealEquivZorn.injective
  apply canonicalVectorEquiv.injective
  exact hZorn

/-- The operator lift resolves into the two established chiral sheet actions. -/
theorem twistorOperatorLift_chiral_decomposition (z : Twistor4) :
    twistorOperatorLift z =
    leftMultiplication (canonicalVectorEquiv (plusZornMap z.1)) +
        leftMultiplication (canonicalVectorEquiv (minusZornMap z.2)) := by
  change leftMultiplication (canonicalVectorEquiv (twistorRealEquivZorn z)) = _
  rw [twistor_zorn_sheet_decomposition]
  change leftMultiplication
    (canonicalVectorEquiv (plusZornMap z.1) + canonicalVectorEquiv (minusZornMap z.2)) = _
  exact map_add (leftMultiplication :
    InfoGeometry.Algebra.ZornVectorMatrix ℝ →ₗ[ℝ]
      Module.End ℝ (InfoGeometry.Algebra.ZornVectorMatrix ℝ)) _ _

/-- The multiplicativity defect of the operator-valued twistor lift is
precisely the existing Zorn multiplication defect. This identifies the
obstruction without erasing nonassociativity. -/
theorem twistorOperatorLift_product_defect (z w : Twistor4) :
    twistorOperatorLift (twistorMul z w) -
        twistorOperatorLift z * twistorOperatorLift w =
      multiplicationDefect (twistorZornLinearMap z) (twistorZornLinearMap w) := by
  change leftMultiplication (twistorZornLinearMap (twistorMul z w)) -
    leftMultiplication (twistorZornLinearMap z) * leftMultiplication (twistorZornLinearMap w) = _
  rw [twistorZornLinearMap_mul]
  rfl

/-- A concrete nonzero operator defect is already present on the twistor
preimages of the native `U 0` and `U 1` Zorn directions. -/
def twistorPreimageU (i : Fin 3) : Twistor4 :=
  twistorRealEquivZorn.symm (canonicalVectorEquiv.symm (InfoGeometry.Algebra.ZornVectorMatrix.U i))

theorem twistorOperatorLift_U01_defect_ne_zero :
    twistorOperatorLift (twistorMul (twistorPreimageU 0) (twistorPreimageU 1)) -
        twistorOperatorLift (twistorPreimageU 0) *
          twistorOperatorLift (twistorPreimageU 1) ≠ 0 := by
  rw [twistorOperatorLift_product_defect]
  simpa [twistorPreimageU, twistorZornLinearMap, canonicalZornToVectorLinearMap,
    LinearMap.comp_apply] using multiplicationDefect_U01_ne_zero

end InfoGeometry.Twistor.TwistorOperatorLift
