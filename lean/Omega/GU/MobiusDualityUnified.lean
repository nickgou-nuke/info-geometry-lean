import Omega.GU.U1ThroatIdentity

namespace Omega.GU

/-- Paper-facing GU wrapper for the unified Möbius duality package.
    prop:mobius-duality-unified -/
theorem paper_gut_mobius_duality_unified
    (u : ℝ) (hu : 0 < u) (hfixed : u = 1 / u)
    (cayleySignFlip poleBarrierBoundaryNormalization : Prop)
    (hcayley : cayleySignFlip)
    (hpole : poleBarrierBoundaryNormalization) :
    u = 1 ∧ cayleySignFlip ∧ poleBarrierBoundaryNormalization := by
  have hu1 : u = 1 := by
    exact (Omega.GU.U1ThroatIdentity.paper_gut_u1_throat_identity_package hu).mp hfixed
  exact ⟨hu1, hcayley, hpole⟩

end Omega.GU
