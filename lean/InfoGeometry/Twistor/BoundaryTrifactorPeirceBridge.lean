import InfoGeometry.Twistor.ChiralTwistorZornCoupling
import InfoGeometry.Algebra.Zorn.G2TrifactorSU3

/-!
# Boundary trifactor projectors and chiral twistor sheet poles

The Zorn trifactor owner already contains two diagonal projectors `OP1`, `OP2`
which are idempotent and satisfy the cubic/tripotent identity `P³=P`.  The
chiral twistor/Zorn owner already identifies the scalar axes of the two Penrose
spinor sheets with the canonical Zorn poles `zornPlus`, `zornMinus`.

This file proves that these are the same two boundary projectors.  It therefore
connects the micro-polarized twistor sheets to the native trifactor/tripotent
operator geometry without introducing a new projector carrier or product.
-/

noncomputable section

namespace InfoGeometry.Twistor.BoundaryTrifactorPeirceBridge

open InfoGeometry.Twistor.ChiralTwistorZornCoupling
open InfoGeometry.Twistor.ChiralTwistorPeirceSheets
open InfoGeometry.Algebra.Zorn.G2TrifactorSU3
open InfoGeometry.Canonical.ZornMatrix

/-- The upper trifactor projector is literally the positive Peirce pole. -/
theorem OP1_eq_zornPlus :
    (OP1 : ZMat ℝ) = zornPlus := by
  rfl

/-- The lower trifactor projector is literally the negative Peirce pole. -/
theorem OP2_eq_zornMinus :
    (OP2 : ZMat ℝ) = zornMinus := by
  rfl

/-- Positive chiral twistor scalar axis lands on the upper trifactor projector. -/
theorem plus_twistor_pole_eq_OP1 :
    plusZornMap sheetScalarSpinor = (OP1 : ZMat ℝ) := by
  rw [plus_scalar_axis_zorn, OP1_eq_zornPlus]

/-- Negative chiral twistor scalar axis lands on the lower trifactor projector. -/
theorem minus_twistor_pole_eq_OP2 :
    minusZornMap sheetScalarSpinor = (OP2 : ZMat ℝ) := by
  rw [minus_scalar_axis_zorn, OP2_eq_zornMinus]

/-- The positive twistor sheet pole is an idempotent under the canonical
trifactor Zorn product. -/
theorem plus_twistor_pole_idempotent :
    zMul (plusZornMap sheetScalarSpinor) (plusZornMap sheetScalarSpinor) =
      plusZornMap sheetScalarSpinor := by
  rw [plus_twistor_pole_eq_OP1]
  exact op1_idempotent

/-- The negative twistor sheet pole is an idempotent under the canonical
trifactor Zorn product. -/
theorem minus_twistor_pole_idempotent :
    zMul (minusZornMap sheetScalarSpinor) (minusZornMap sheetScalarSpinor) =
      minusZornMap sheetScalarSpinor := by
  rw [minus_twistor_pole_eq_OP2]
  exact op2_idempotent

/-- Positive boundary pole satisfies the cubic/tripotent identity. -/
theorem plus_twistor_pole_tripoten​​t :
    zMul (zMul (plusZornMap sheetScalarSpinor) (plusZornMap sheetScalarSpinor))
        (plusZornMap sheetScalarSpinor) = plusZornMap sheetScalarSpinor := by
  rw [plus_twistor_pole_eq_OP1]
  exact op1_cubic

/-- Negative boundary pole satisfies the cubic/tripotent identity. -/
theorem minus_twistor_pole_tripoten​​t :
    zMul (zMul (minusZornMap sheetScalarSpinor) (minusZornMap sheetScalarSpinor))
        (minusZornMap sheetScalarSpinor) = minusZornMap sheetScalarSpinor := by
  rw [minus_twistor_pole_eq_OP2]
  exact op2_cubic

end InfoGeometry.Twistor.BoundaryTrifactorPeirceBridge
