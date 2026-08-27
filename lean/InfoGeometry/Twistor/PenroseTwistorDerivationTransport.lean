import InfoGeometry.Algebra.ZornDerivationBridge
import InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge
import InfoGeometry.Twistor.PenroseIncidence
import InfoGeometry.Twistor.RealSplitOctonionCarrierBridge
import InfoGeometry.Twistor.ChiralTwistorPeirceSheets

/-!
# Transport of native Zorn standard derivations to the real twistor carrier

This owner records only linear transport.  It does not claim that the
induced operation on the twistor carrier is an independently defined Penrose
product.
-/

noncomputable section

namespace InfoGeometry.Twistor.PenroseTwistorDerivationTransport

open InfoGeometry.Algebra
open InfoGeometry.Algebra.Zorn
open InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge
open InfoGeometry.Twistor.PenroseIncidence
open InfoGeometry.Twistor.RealSplitOctonionCarrierBridge
open InfoGeometry.Twistor.ChiralTwistorPeirceSheets

abbrev VZ := ZornVectorMatrix ℝ
abbrev TwistorCarrier := Twistor4

noncomputable def canonicalVectorLinearEquiv :
    InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge.CanonicalZorn ≃ₗ[ℝ] VZ where
  toFun := canonicalVectorEquiv
  invFun := canonicalVectorEquiv.symm
  left_inv := canonicalVectorEquiv.left_inv
  right_inv := canonicalVectorEquiv.right_inv
  map_add' := by
    intro x y
    exact canonicalVectorEquiv_add x y
  map_smul' := by
    intro r x
    exact canonicalVectorEquiv_smul r x

noncomputable def twistorToVector : TwistorCarrier ≃ₗ[ℝ] VZ :=
  twistorRealEquivZorn.trans canonicalVectorLinearEquiv

theorem twistorToVector_sheet_decomposition (Z : TwistorCarrier) :
    twistorToVector Z =
      canonicalVectorEquiv (plusZornMap Z.1 + minusZornMap Z.2) := by
  change canonicalVectorEquiv (twistorRealEquivZorn Z) = _
  rw [twistor_zorn_sheet_decomposition]

noncomputable def transportedStanDerivation (a b : VZ) :
    TwistorCarrier →ₗ[ℝ] TwistorCarrier :=
  twistorToVector.symm.toLinearMap.comp
    ((zornStanDerivation a b).toLinearMap.comp twistorToVector.toLinearMap)

/-- The multiplication transported along the real linear equivalence.  This is
    deliberately named separately from any Penrose product: it is induced by
    the Zorn carrier, not an identification theorem for a native twistor
    multiplication. -/
noncomputable def transportedMultiplication (x y : TwistorCarrier) : TwistorCarrier :=
  twistorToVector.symm (twistorToVector x * twistorToVector y)

/-- The transported product carries the native Zorn associator defect back to
    the twistor carrier.  This is an algebraic transport statement, not a
    claim that the Penrose carrier has an independently defined product. -/
theorem transportedMultiplication_associator (x y z : TwistorCarrier) :
    transportedMultiplication (transportedMultiplication x y) z -
        transportedMultiplication x (transportedMultiplication y z) =
      twistorToVector.symm
        (_root_.associator (twistorToVector x) (twistorToVector y)
          (twistorToVector z)) := by
  apply twistorToVector.injective
  simp [transportedMultiplication, sub_eq_add_neg, _root_.associator_apply]

theorem transportedMultiplication_associator_eq_zero_iff
    (x y z : TwistorCarrier) :
    transportedMultiplication (transportedMultiplication x y) z -
        transportedMultiplication x (transportedMultiplication y z) = 0 ↔
      _root_.associator (twistorToVector x) (twistorToVector y)
        (twistorToVector z) = 0 := by
  rw [transportedMultiplication_associator]
  exact twistorToVector.symm.map_eq_zero_iff

theorem transportedMultiplication_add_left (x y z : TwistorCarrier) :
    transportedMultiplication (x + y) z =
      transportedMultiplication x z + transportedMultiplication y z := by
  apply twistorToVector.injective
  simp only [transportedMultiplication, LinearEquiv.apply_symm_apply, map_add]
  exact ZornVectorMatrix.add_mul (twistorToVector x) (twistorToVector y) (twistorToVector z)

theorem transportedMultiplication_add_right (x y z : TwistorCarrier) :
    transportedMultiplication x (y + z) =
      transportedMultiplication x y + transportedMultiplication x z := by
  apply twistorToVector.injective
  simp only [transportedMultiplication, LinearEquiv.apply_symm_apply, map_add]
  exact ZornVectorMatrix.mul_add (twistorToVector x) (twistorToVector y) (twistorToVector z)

theorem transportedMultiplication_smul_left (r : ℝ) (x y : TwistorCarrier) :
    transportedMultiplication (r • x) y =
      r • transportedMultiplication x y := by
  apply twistorToVector.injective
  simp only [transportedMultiplication, LinearEquiv.apply_symm_apply,
    map_smul]
  exact ZornVectorMatrix.smul_mul r (twistorToVector x) (twistorToVector y)

theorem transportedMultiplication_smul_right (r : ℝ) (x y : TwistorCarrier) :
    transportedMultiplication x (r • y) =
      r • transportedMultiplication x y := by
  apply twistorToVector.injective
  simp only [transportedMultiplication, LinearEquiv.apply_symm_apply,
    map_smul]
  exact ZornVectorMatrix.mul_smul r (twistorToVector x) (twistorToVector y)

/-- Explicit contract for identifying a future native Penrose product with the
transport-induced product.  The equality is data, not an unproved theorem. -/
structure NativeProductComparison where
  product : TwistorCarrier → TwistorCarrier → TwistorCarrier
  product_eq_transport : ∀ x y, product x y = transportedMultiplication x y

theorem transportedStanDerivation_intertwines
    (a b : VZ) (z : TwistorCarrier) :
    twistorToVector (transportedStanDerivation a b z) =
      zornStanDerivation a b (twistorToVector z) := by
  simp [transportedStanDerivation]

theorem transportedStanDerivation_leibniz
    (a b : VZ) (x y : TwistorCarrier) :
    transportedStanDerivation a b (transportedMultiplication x y) =
      transportedMultiplication (transportedStanDerivation a b x) y +
        transportedMultiplication x (transportedStanDerivation a b y) := by
  apply twistorToVector.injective
  simp [transportedMultiplication, transportedStanDerivation]
  exact (zornStanDerivation a b).leibniz' (twistorToVector x) (twistorToVector y)

theorem native_product_derivation_leibniz
    (P : NativeProductComparison) (a b : VZ) (x y : TwistorCarrier) :
    transportedStanDerivation a b (P.product x y) =
      P.product (transportedStanDerivation a b x) y +
        P.product x (transportedStanDerivation a b y) := by
  rw [P.product_eq_transport, P.product_eq_transport, P.product_eq_transport]
  exact transportedStanDerivation_leibniz a b x y

theorem transportedStanDerivation_normal_form
    (a b : VZ) (z : TwistorCarrier) :
    twistorToVector (transportedStanDerivation a b z) =
      ((a * b - b * a) * twistorToVector z -
          twistorToVector z * (a * b - b * a)) -
        3 • _root_.associator a b (twistorToVector z) := by
  rw [transportedStanDerivation_intertwines]
  exact zornStanDerivation_apply_normal_form a b (twistorToVector z)

end InfoGeometry.Twistor.PenroseTwistorDerivationTransport
