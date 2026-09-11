import InfoGeometry.Canonical.MealyAlgebraicIdentityConsequences
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.SplitQuaternionAssociativeCoassociativeCalibrationBridge

namespace InfoGeometry.Canonical

/-!
# Mealy consequences over the native split-octonion calibration owner

This bridge keeps the noncommutative split-octonion geometry as the source of
the data.  It only packages the scalar Mealy-style consequences of the native
standard associative slice.
-/

namespace MealySplitOctonionBridge

/-- The standard associative split-octonion triple satisfies the Mealy bound. -/
theorem standard_associative_three_form_mealy_consequence :
    (1 ≤ (canonicalSplitG2ThreeFormValue
      SplitQuaternionAssociativeCoassociativeCalibrationBridge.imagI
      SplitQuaternionAssociativeCoassociativeCalibrationBridge.imagJ
      SplitQuaternionAssociativeCoassociativeCalibrationBridge.imagK : ℚ)^2) ∧
    ((canonicalSplitG2ThreeFormValue
      SplitQuaternionAssociativeCoassociativeCalibrationBridge.imagI
      SplitQuaternionAssociativeCoassociativeCalibrationBridge.imagJ
      SplitQuaternionAssociativeCoassociativeCalibrationBridge.imagK : ℚ)^2 = 1 ↔ (0 : ℚ) = 0) := by
  have h_identity :
      (canonicalSplitG2ThreeFormValue
        SplitQuaternionAssociativeCoassociativeCalibrationBridge.imagI
        SplitQuaternionAssociativeCoassociativeCalibrationBridge.imagJ
        SplitQuaternionAssociativeCoassociativeCalibrationBridge.imagK : ℚ)^2 =
        1 - (1 / 4 : ℚ) * 0 := by
    rw [SplitQuaternionAssociativeCoassociativeCalibrationBridge.standard_associative_three_form_value]
    norm_num
  have h_nonpos : (0 : ℚ) ≤ 0 := by linarith
  simpa using
    (mealy_algebraic_identity_consequences
      (phiSq := (canonicalSplitG2ThreeFormValue
        SplitQuaternionAssociativeCoassociativeCalibrationBridge.imagI
        SplitQuaternionAssociativeCoassociativeCalibrationBridge.imagJ
        SplitQuaternionAssociativeCoassociativeCalibrationBridge.imagK : ℚ)^2)
      (q := (0 : ℚ))
      h_identity
      h_nonpos)

/-- The standard coassociative generator triple has vanishing 3-form readout. -/
theorem standard_coassociative_three_form_mealy_shadow :
    canonicalSplitG2ThreeFormValue
      SplitQuaternionAssociativeCoassociativeCalibrationBridge.imagIL
      SplitQuaternionAssociativeCoassociativeCalibrationBridge.imagJL
      SplitQuaternionAssociativeCoassociativeCalibrationBridge.imagKL = 0 := by
  simpa using
    SplitQuaternionAssociativeCoassociativeCalibrationBridge.standard_coassociative_three_form_value

end MealySplitOctonionBridge

end InfoGeometry.Canonical
