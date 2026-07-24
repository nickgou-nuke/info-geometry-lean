import InfoGeometry.Canonical.SplitCliffordSourceWickBase
import InfoGeometry.Canonical.SplitCliffordSourceWickVacuum

/-!
# InfoGeometry.Canonical.SplitCliffordSourceWickBaseExternalBridge

Bridge from the finite `M₂(ℝ)` Wick base atom to the existing external
Heisenberg/Sugawara readout lane.

No new current algebra construction is introduced here.  This file only states
the shared base-case normalization shape:

* local finite atom: commutator on vacuum gives the mode-one seed;
* external charged-Fock lane: `J₁`/`J₋₁` commutator equals `1 • id`.
-/

namespace InfoGeometry.Canonical.SplitCliffordSourceWickBaseExternalBridge

open InfoGeometry.Canonical.SplitCliffordSourceWickBase
open InfoGeometry.Canonical.SplitCliffordSourceWickVacuum

/--
Finite local Wick base-case, rewritten in mode-one normalization form.
-/
theorem local_wick_mode_one_seed :
    (a * aDag - aDag * a) * vac = (1 : ℝ) • vac := by
  simpa using local_wick_vacuum_commutator

/--
External charged-Fock mode-one base commutator readout.

This is exactly the existing owner theorem from
`SplitCliffordSourceWickVacuum.ExternalLaneReadout`, specialized at `m = 1`.
-/
theorem external_chargedFock_mode_one_commutator
    (𝕜 : Type*) [Field 𝕜] [CharZero 𝕜] (α : 𝕜) :
    let M :
      InfoGeometry.Canonical.CurrentSugawaraBridge.CurrentSugawaraMorphism 𝕜
        (VirasoroProject.ChargedFockSpace 𝕜 α) :=
      InfoGeometry.Canonical.CurrentSugawaraBridge.CurrentSugawaraMorphism.ofHeisenberg
        (InfoGeometry.Canonical.CurrentSugawaraBridge.chargedFockSpaceCurrentHeisenbergRep 𝕜 α)
    (M.heisenberg.J 1).commutator (M.heisenberg.J (-1)) =
      (1 : 𝕜) •
        (1 :
          VirasoroProject.ChargedFockSpace 𝕜 α →ₗ[𝕜]
            VirasoroProject.ChargedFockSpace 𝕜 α) := by
  simpa using chargedFock_current_commutator_base_via_morphism (𝕜 := 𝕜) α (1 : Int)

end InfoGeometry.Canonical.SplitCliffordSourceWickBaseExternalBridge

