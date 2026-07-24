import InfoGeometry.Canonical.DrazinCentralizerErlangen

/-!
# Modular Mirror Horizon

This file formalizes the corrected algebraic reading of the modular mirror
horizon:

* the horizon is not the center in general;
* the neutral sector is a modularly fixed / compressed / projector-selected
  boundary sector;
* the horizon itself is a member of that sector;
* every member of that sector is a modular zero mode.

The file uses the existing Drazin-centralizer owner surface, so it stays in the
boundary-sector language already supported by the repository.
-/

noncomputable section

namespace InfoGeometry.Canonical.ModularMirrorHorizon

open InfoGeometry.Canonical.DrazinCentralizerErlangen

/-! ## Boundary sector definitions -/

variable {Obs : Type*} [Ring Obs] [Star Obs] [SMul ℂ Obs]

/--
The modular mirror horizon sector.

This is the projection-selected compressed centralizer, not the algebraic
center.  It is the corrected neutral sector for the modular mirror boundary.
-/
def horizonBoundarySector (S : DrazinCentralizerSanctuary Obs) : Set Obs :=
  {x | InDrazinCompressedCentralizer S.flow S.horizon x}

@[simp]
theorem mem_horizonBoundarySector_iff
    (S : DrazinCentralizerSanctuary Obs) (x : Obs) :
    x ∈ horizonBoundarySector S ↔
      InDrazinCompressedCentralizer S.flow S.horizon x :=
  Iff.rfl

/-- The horizon support projector is idempotent. -/
theorem horizonSupport_idempotent
    (S : DrazinCentralizerSanctuary Obs) :
    S.horizon.p * S.horizon.p = S.horizon.p :=
  InfoGeometry.Canonical.DrazinModularPersistence.DrazinSupportData.p_idempotent S.horizon

/-- The horizon support projector is self-adjoint. -/
theorem horizonSupport_selfAdjoint
    (S : DrazinCentralizerSanctuary Obs) :
    star S.horizon.p = S.horizon.p :=
  S.horizon.p_self_adjoint

/--
The horizon itself belongs to the corrected boundary sector.

This is the formal version of "the horizon is the neutral sector selected by
modular data and projections."
-/
theorem horizon_mem_boundarySector
    (S : DrazinCentralizerSanctuary Obs) :
    S.horizon.p ∈ horizonBoundarySector S :=
  horizon_mem_compressed_centralizer S.flow S.horizon S.centralizer_horizon

/-- Every element of the boundary sector is a horizon zero mode. -/
theorem boundarySector_zeroMode
    (S : DrazinCentralizerSanctuary Obs) (x : Obs)
    (hx : x ∈ horizonBoundarySector S) :
    InfoGeometry.Canonical.DrazinModularPersistence.IsHorizonZeroMode S.flow S.horizon x :=
  compressed_centralizer_is_horizon_zero_mode S.flow S.horizon x hx

/-- The horizon sector is exactly the compressed centralizer. -/
theorem horizonBoundarySector_eq_compressedCentralizer
    (S : DrazinCentralizerSanctuary Obs) (x : Obs) :
    x ∈ horizonBoundarySector S ↔
      InDrazinCompressedCentralizer S.flow S.horizon x :=
  Iff.rfl

end InfoGeometry.Canonical.ModularMirrorHorizon
