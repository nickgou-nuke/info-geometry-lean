import InfoGeometry.Conformal.SchwarzianApollonius
import InfoGeometry.Algebra.FiniteSpinAlgebra

namespace InfoGeometry.Canonical.SchwarzianApolloniusCapstone

open InfoGeometry.Conformal.SchwarzianApollonius

set_option linter.unusedVariables false

/-- Public capstone assembled from the existing local Schwarzian owners. -/
theorem verification_capstone (s : ℂ) (hs : s + ⟨1 / 2, 0⟩ ≠ 0) (c : ℂ) :
    (apolloniusDeriv2 s / apolloniusDeriv1 s = apolloniusAffineConnection s) ∧
      (2 / (s + ⟨1 / 2, 0⟩) ^ 2 -
        (1 / 2 : ℂ) * (apolloniusAffineConnection s) ^ 2 = 0) ∧
      (- (c / 12) * (2 / (s + ⟨1 / 2, 0⟩) ^ 2 -
        (1 / 2 : ℂ) * (apolloniusAffineConnection s) ^ 2) = 0) := by
  exact ⟨apollonius_deriv2_div_deriv1 s hs,
    apollonius_schwarzian_identity s hs,
    apollonius_virasoro_anomaly_zero s hs c⟩

end InfoGeometry.Canonical.SchwarzianApolloniusCapstone
