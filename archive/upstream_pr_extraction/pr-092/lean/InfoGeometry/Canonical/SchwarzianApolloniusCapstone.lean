import InfoGeometry.Conformal.SchwarzianApollonius

namespace InfoGeometry.Canonical.SchwarzianApolloniusCapstone

open InfoGeometry.Conformal.SchwarzianApollonius

set_option linter.unusedVariables false

theorem verification_capstone (s : ℂ) (hs : s + ⟨1 / 2, 0⟩ ≠ 0) (c : ℂ) :
    (apolloniusDeriv2 s / apolloniusDeriv1 s = apolloniusAffineConnection s) ∧
      (2 / (s + ⟨1 / 2, 0⟩) ^ 2 -
        (1 / 2 : ℂ) * (apolloniusAffineConnection s) ^ 2 = 0) ∧
      (- (c / 12) * (2 / (s + ⟨1 / 2, 0⟩) ^ 2 -
        (1 / 2 : ℂ) * (apolloniusAffineConnection s) ^ 2) = 0) := by
  exact grand_apollonius_schwarzian_synthesis s hs c

end InfoGeometry.Canonical.SchwarzianApolloniusCapstone
