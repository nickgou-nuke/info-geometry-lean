import InfoGeometry.Canonical.MealyAlgebraicIdentityConsequences
import InfoGeometry.Canonical.SplitQuaternionAssociativeCoassociativeCalibrationBridge
import InfoGeometry.Canonical.MealySplitOctonionBridge

/-!
# Harvey--Lawson deformation bridge over the native split-octonion owners

This file intentionally does not introduce a new calibration carrier.
It packages the already verified Mealy consequences and split-octonion
readouts under a local bridge name so downstream imports can depend on a
theorem-safe layer rather than on a speculative abstraction.
-/

namespace InfoGeometry.Canonical

namespace HarveyLawsonDiracDeformation

/-- The standard associative split-octonion slice satisfies the Mealy-style
volume lower bound through the existing native bridge. -/
theorem standard_associative_three_form_harvey_lawson_consequence :
    (1 ≤ (canonicalSplitG2ThreeFormValue
      SplitQuaternionAssociativeCoassociativeCalibrationBridge.imagI
      SplitQuaternionAssociativeCoassociativeCalibrationBridge.imagJ
      SplitQuaternionAssociativeCoassociativeCalibrationBridge.imagK : ℚ)^2) ∧
    ((canonicalSplitG2ThreeFormValue
      SplitQuaternionAssociativeCoassociativeCalibrationBridge.imagI
      SplitQuaternionAssociativeCoassociativeCalibrationBridge.imagJ
      SplitQuaternionAssociativeCoassociativeCalibrationBridge.imagK : ℚ)^2 = 1 ↔ (0 : ℚ) = 0) :=
  MealySplitOctonionBridge.standard_associative_three_form_mealy_consequence

/-- The standard coassociative generator triple has vanishing 3-form readout. -/
theorem standard_coassociative_three_form_harvey_lawson_shadow :
    canonicalSplitG2ThreeFormValue
      SplitQuaternionAssociativeCoassociativeCalibrationBridge.imagIL
      SplitQuaternionAssociativeCoassociativeCalibrationBridge.imagJL
      SplitQuaternionAssociativeCoassociativeCalibrationBridge.imagKL = 0 :=
  MealySplitOctonionBridge.standard_coassociative_three_form_mealy_shadow

end HarveyLawsonDiracDeformation

end InfoGeometry.Canonical
