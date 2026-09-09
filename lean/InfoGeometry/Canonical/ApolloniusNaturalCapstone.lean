import InfoGeometry.Projective.ApolloniusNatural

namespace InfoGeometry.Canonical.ApolloniusNaturalCapstone

open InfoGeometry.Projective.ApolloniusNatural
open Complex

set_option linter.unusedVariables false

theorem verification_capstone (ξ θ : ℝ) :
    (normSq (apolloniusRay ξ θ).1 = Real.exp (2 * ξ)) ∧
      (projectiveSignatureQuotient (apolloniusRay ξ θ) = Real.tanh ξ) ∧
      (projectiveSignatureQuotient (apolloniusRay 0 θ) = 0) ∧
      (projectiveSignatureQuotient
        ((apolloniusRay ξ θ).2, (apolloniusRay ξ θ).1) = - Real.tanh ξ) := by
  exact grand_apollonius_natural_projective_synthesis ξ θ

end InfoGeometry.Canonical.ApolloniusNaturalCapstone
