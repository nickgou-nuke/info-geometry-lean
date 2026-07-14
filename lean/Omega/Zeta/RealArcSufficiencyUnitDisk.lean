import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper-facing wrapper for the real-arc sufficiency argument: equality on `(0,1)` forces the
meromorphic identity on the full unit disk, and the spectral poles are removable because the
difference `G - A_∞` is holomorphic.
    prop:real-arc-sufficiency-unit-disk -/
theorem paper_real_arc_sufficiency_unit_disk
    (holomorphicG holomorphicAinfty meromorphicS vanishesOnRealArc identityExtendsToDisk
      spectralPolesAreRemovable : Prop)
    (holomorphicG_h : holomorphicG)
    (holomorphicAinfty_h : holomorphicAinfty)
    (meromorphicS_h : meromorphicS)
    (vanishesOnRealArc_h : vanishesOnRealArc)
    (deriveIdentityExtendsToDisk :
      holomorphicG → holomorphicAinfty → meromorphicS → vanishesOnRealArc →
        identityExtendsToDisk)
    (deriveSpectralPolesAreRemovable :
      holomorphicG → holomorphicAinfty → identityExtendsToDisk → spectralPolesAreRemovable) :
    identityExtendsToDisk ∧ spectralPolesAreRemovable := by
  have hIdentity : identityExtendsToDisk :=
    deriveIdentityExtendsToDisk holomorphicG_h holomorphicAinfty_h meromorphicS_h
      vanishesOnRealArc_h
  exact ⟨hIdentity,
    deriveSpectralPolesAreRemovable holomorphicG_h holomorphicAinfty_h hIdentity⟩

end Omega.Zeta
