/- SPDX-License-Identifier: Apache-2.0 -/

import InfoGeometry.Automorphic.SiegelResonance

namespace InfoGeometry.Canonical

open InfoGeometry.Automorphic.SiegelResonance

/-- Canonical projection capstone for the Siegel resonance boundary extraction. -/
theorem siegel_resonance_canonical_capstone
    (Ker Boundary : Type*)
    [AddCommGroup Ker] [Module ℝ Ker]
    [AddCommGroup Boundary] [Module ℝ Boundary] :
    let W := ofProd Ker Boundary
    -- 1. Section property: 𝔖 ∘ ℰ = id
    (W.siegel.comp W.eisenstein = LinearMap.id) ∧
    -- 2. Surjectivity of Siegel boundary operator
    Function.Surjective W.siegel ∧
    -- 3. Projector completeness: Π_bdry + ℜ_P = I
    (W.boundaryProjector + W.cuspidalProjector = LinearMap.id) ∧
    -- 4. Cuspidal core annihilation: 𝔖 ∘ ℜ_P = 0
    (W.siegel.comp W.cuspidalProjector = 0) ∧
    -- 5. Exactness: range ℜ_P = ker 𝔖
    (LinearMap.range W.cuspidalProjector = LinearMap.ker W.siegel) ∧
    -- 6. Canonical kernel identification
    (LinearMap.ker W.siegel = LinearMap.range (prodInl Ker Boundary)) := by
  intro W
  exact ⟨
    W.section_property,
    W.siegel_surjective,
    W.projector_sum,
    W.siegel_annihilates_cuspidal_core,
    W.range_cuspidalProjector_eq_ker_siegel,
    ofProd_ker_siegel Ker Boundary
  ⟩

end InfoGeometry.Canonical
