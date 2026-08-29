/- SPDX-License-Identifier: Apache-2.0 -/

import InfoGeometry.Projective.ApolloniusNatural

namespace InfoGeometry.Canonical

open InfoGeometry.Projective.ApolloniusNatural Complex Real

/-- 🏆 GRAND CANONICAL CAPSTONE: Natural Apollonian Projective Geometry Synthesis -/
theorem grand_canonical_apollonius_natural_projective_synthesis (ξ θ : ℝ) :
    (normSq (apolloniusRay ξ θ).1 = Real.exp (2 * ξ)) ∧
    (projectiveSignatureQuotient (apolloniusRay ξ θ) = Real.tanh ξ) ∧
    (projectiveSignatureQuotient (apolloniusRay ξ θ) = 0 ↔ ξ = 0) ∧
    (projectiveSignatureQuotient (1, (apolloniusRay ξ θ).1) = - Real.tanh ξ) :=
  grand_apollonius_natural_projective_synthesis ξ θ

end InfoGeometry.Canonical
