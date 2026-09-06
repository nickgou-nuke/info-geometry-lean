import InfoGeometry.Spectral.MontgomeryPairCorrelation

namespace InfoGeometry.Canonical.MontgomeryPairCorrelationCapstone

open InfoGeometry.Spectral.MontgomeryPairCorrelation

theorem capstone_montgomery_pair_correlation_synthesis (k : ℤ) (hk : k ≠ 0) (s : ℝ) :
    (montgomeryPairCorrelation 0 = 0) ∧
    (montgomeryPairCorrelation (-s) = montgomeryPairCorrelation s) ∧
    (montgomeryPairCorrelation (k : ℝ) = 1) :=
  grand_montgomery_pair_correlation_synthesis k hk s

end InfoGeometry.Canonical.MontgomeryPairCorrelationCapstone
