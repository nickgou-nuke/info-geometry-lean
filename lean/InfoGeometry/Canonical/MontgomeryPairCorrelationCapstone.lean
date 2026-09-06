import InfoGeometry.Spectral.MontgomeryPairCorrelation

namespace InfoGeometry.Canonical.MontgomeryPairCorrelationCapstone

open InfoGeometry.Spectral.MontgomeryPairCorrelation

/-- Canonical packaging of the elementary Montgomery pair-correlation packet. -/
theorem capstone_montgomery_pair_correlation_synthesis (k : ℤ) (hk : k ≠ 0) (s : ℝ) :
    (montgomeryPairCorrelation 0 = 0) ∧
    (montgomeryPairCorrelation (-s) = montgomeryPairCorrelation s) ∧
    (montgomeryPairCorrelation (k : ℝ) = 1) := by
  exact ⟨montgomery_at_zero, montgomery_even s, montgomery_at_integer k hk⟩

end InfoGeometry.Canonical.MontgomeryPairCorrelationCapstone
