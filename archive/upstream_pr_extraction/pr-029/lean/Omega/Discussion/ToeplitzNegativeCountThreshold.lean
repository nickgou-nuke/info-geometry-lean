import Mathlib.Tactic

namespace Omega.Discussion

/-- Carrier data for the negative-count threshold argument. -/
structure ToeplitzNegativeCountThresholdData where
  thresholdN : ℕ
  largeN : ℕ
  smallN : ℕ
  negativeCount : ℕ → ℕ
  ambientCount : ℕ → ℕ

/-- Beyond the stabilization threshold the full negative count is visible, while below the
threshold a negative direction remains unresolved. -/
theorem paper_discussion_toeplitz_negative_count_threshold
    (D : ToeplitzNegativeCountThresholdData)
    (largeN_ge_threshold : D.thresholdN ≤ D.largeN)
    (stabilization : ∀ N ≥ D.thresholdN,
      D.negativeCount N = D.ambientCount N)
    (unresolvedMode : D.negativeCount D.smallN < D.ambientCount D.smallN) :
    D.negativeCount D.largeN = D.ambientCount D.largeN ∧
      D.negativeCount D.smallN < D.ambientCount D.smallN := by
  exact ⟨stabilization D.largeN largeN_ge_threshold, unresolvedMode⟩

end Omega.Discussion
