import Omega.TypedAddressBiaxialCompletion.ComovingPronyThreshold

namespace Omega.UnitCirclePhaseArithmetic

/-- Paper-facing unit-circle restatement of the typed-address Prony-threshold window lengths.
    thm:unit-circle-comoving-prony-threshold -/
theorem paper_unit_circle_comoving_prony_threshold
    (kappa rankDetectionWindow exactRecoveryWindow : ℕ)
    (rankDetectionWindow_eq : rankDetectionWindow = 2 * kappa - 1)
    (exactRecoveryWindow_eq : exactRecoveryWindow = 2 * kappa) :
    rankDetectionWindow = 2 * kappa - 1 ∧ exactRecoveryWindow = 2 * kappa := by
  simpa using
    Omega.TypedAddressBiaxialCompletion.paper_typed_address_biaxial_completion_comoving_prony_threshold
      kappa rankDetectionWindow exactRecoveryWindow rankDetectionWindow_eq exactRecoveryWindow_eq

end Omega.UnitCirclePhaseArithmetic
