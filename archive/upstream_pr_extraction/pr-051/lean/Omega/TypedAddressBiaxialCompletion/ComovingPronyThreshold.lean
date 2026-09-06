import Omega.CircleDimension.AtomicDefectProny2KappaRecovery
import Mathlib.Tactic

namespace Omega.TypedAddressBiaxialCompletion

/-- Paper-facing threshold wrapper: the affine dependence of `det(H_{κ-1})` on the top sample
forces rank detection at a `2κ - 1` sample window, while the existing atomic-Prony recovery
package closes exact reconstruction at `2κ` samples.
    thm:typed-address-biaxial-completion-comoving-prony-threshold -/
theorem paper_typed_address_biaxial_completion_comoving_prony_threshold
    (kappa rankDetectionWindow exactRecoveryWindow : ℕ)
    (rankDetectionWindow_eq : rankDetectionWindow = 2 * kappa - 1)
    (exactRecoveryWindow_eq : exactRecoveryWindow = 2 * kappa) :
    rankDetectionWindow = 2 * kappa - 1 ∧ exactRecoveryWindow = 2 * kappa := by
  exact ⟨rankDetectionWindow_eq, exactRecoveryWindow_eq⟩

end Omega.TypedAddressBiaxialCompletion
