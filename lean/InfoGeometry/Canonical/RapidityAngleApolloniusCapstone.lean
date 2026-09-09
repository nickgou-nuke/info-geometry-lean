/- SPDX-License-Identifier: Apache-2.0 -/

import InfoGeometry.ParaKahler.RapidityAngleApollonius

namespace InfoGeometry.Canonical

open InfoGeometry.ParaKahler.RapidityAngleApollonius Real Complex

/-- Canonical synthesis of the rapidity/angle Apollonius owner laws. -/
theorem grand_canonical_rapidity_angle_apollonius_synthesis (γ χ θ : ℝ) :
    (masterPotential χ θ = (1 / 2 : ℝ) * (lightConeU χ θ) * (lightConeV χ θ)) ∧
    (souriauSignature 0 = 0) ∧
    (0 < dikinRapidityMetric χ) ∧
    (dikinRapidityMetric 0 = 2) ∧
    (Complex.normSq (hilbertPolyaMode γ 0 θ) = 1) ∧
    (Complex.normSq (hilbertPolyaMode γ χ θ) = Real.exp (-χ)) := by
  refine ⟨masterPotential_lightCone_factorization χ θ, souriauSignature_zero, ?_⟩
  refine ⟨dikinRapidityMetric_pos χ, dikinRapidityMetric_zero, ?_⟩
  exact ⟨hilbertPolyaMode_equator_unitary γ θ, hilbertPolyaMode_normSq γ χ θ⟩

end InfoGeometry.Canonical
