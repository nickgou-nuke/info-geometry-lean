import Mathlib.Tactic

namespace Omega.Discussion

/-- Beyond the stabilization threshold the full negative count is visible, while below the
threshold a negative direction remains unresolved. -/
theorem paper_discussion_toeplitz_negative_count_threshold
    (thresholdN largeN smallN : ℕ)
    (negativeCount ambientCount : ℕ → ℕ)
    (largeN_ge_threshold : thresholdN ≤ largeN)
    (stabilization : ∀ N ≥ thresholdN,
      negativeCount N = ambientCount N)
    (unresolvedMode : negativeCount smallN < ambientCount smallN) :
    negativeCount largeN = ambientCount largeN ∧
      negativeCount smallN < ambientCount smallN := by
  exact ⟨stabilization largeN largeN_ge_threshold, unresolvedMode⟩

end Omega.Discussion
