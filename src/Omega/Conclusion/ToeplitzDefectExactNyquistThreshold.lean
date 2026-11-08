import Omega.TypedAddressBiaxialCompletion.ComovingPronyThreshold

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-toeplitz-defect-exact-nyquist-threshold`. This is the
Conclusion-level restatement of the typed-address comoving Prony threshold split. -/
theorem paper_conclusion_toeplitz_defect_exact_nyquist_threshold
    (kappa rankDetectionWindow exactRecoveryWindow : ℕ)
    (rankDetectionWindow_eq : rankDetectionWindow = 2 * kappa - 1)
    (exactRecoveryWindow_eq : exactRecoveryWindow = 2 * kappa) :
    rankDetectionWindow = 2 * kappa - 1 ∧ exactRecoveryWindow = 2 * kappa := by
  simpa using
    Omega.TypedAddressBiaxialCompletion.paper_typed_address_biaxial_completion_comoving_prony_threshold
      kappa rankDetectionWindow exactRecoveryWindow rankDetectionWindow_eq exactRecoveryWindow_eq

end Omega.Conclusion
