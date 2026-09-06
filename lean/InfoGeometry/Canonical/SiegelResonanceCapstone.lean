/- SPDX-License-Identifier: Apache-2.0 -/

import InfoGeometry.Automorphic.SiegelResonance

namespace InfoGeometry.Canonical

open InfoGeometry.Automorphic.SiegelResonance

/-- Canonical projection of the finite Siegel boundary decomposition. -/
theorem siegel_resonance_canonical_capstone
    {Bulk Boundary : Type*}
    [AddCommGroup Bulk] [Module ℝ Bulk]
    [AddCommGroup Boundary] [Module ℝ Boundary]
    (W : SiegelEisensteinWitness Bulk Boundary) :
    (W.siegel.comp W.eisenstein = LinearMap.id) ∧
    Function.Surjective W.siegel ∧
    (W.boundaryProjector + W.cuspidalProjector = LinearMap.id) ∧
    (W.siegel.comp W.cuspidalProjector = 0) ∧
    (LinearMap.range W.cuspidalProjector = LinearMap.ker W.siegel) := by
  exact ⟨W.section_axiom, W.siegel_surjective, W.projector_sum,
    W.siegel_annihilates_cuspidal_core,
    W.range_cuspidalProjector_eq_ker_siegel⟩

end InfoGeometry.Canonical
