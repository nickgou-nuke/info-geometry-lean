/- SPDX-License-Identifier: Apache-2.0 -/

/-
# Charged-Fock braid/Virasoro bridge

The repository's concrete Virasoro carrier is the charged Heisenberg Fock
space.  This module specializes the categorical braid-colimit action interface
to that carrier and reuses the existing Sugawara stress modes and bracket.

A compatible finite-stage braid action remains an explicit input.  The module
does not replace it by a trivial action or identify the Fock space with a
categorical colimit without a supplied map.
-/

import InfoGeometry.Categorical.BraidColimitVirasoroAction
import InfoGeometry.Canonical.CurrentSugawaraBridge
import InfoGeometry.External.Virasoro.FockSpaceSugawara

noncomputable section

namespace InfoGeometry.Categorical.ChargedFockBraidVirasoroBridge

open InfoGeometry.Categorical.BraidColimitVirasoroAction
open InfoGeometry.Canonical.CurrentSugawaraBridge
open VirasoroProject

/-- The concrete Fock carrier already owned by the Virasoro modules. -/
abbrev ChargedFockCarrier (𝕜 : Type*) [Field 𝕜] (α : 𝕜) : Type :=
  ChargedFockSpace 𝕜 α

/-- The existing Sugawara stress mode on the charged Fock carrier. -/
noncomputable def chargedFockVirasoroMode
    (𝕜 : Type*) [Field 𝕜] [CharZero 𝕜] (α : 𝕜) (m : ℤ) :
    ChargedFockCarrier 𝕜 α →ₗ[𝕜] ChargedFockCarrier 𝕜 α :=
  CurrentHeisenbergRep.sugawaraStressMode
    (chargedFockSpaceCurrentHeisenbergRep 𝕜 α) m

/-- The charged-Fock stress modes satisfy the existing Virasoro bracket
with the owner-normalized central term. -/
theorem chargedFockVirasoroMode_bracket
    (𝕜 : Type*) [Field 𝕜] [CharZero 𝕜] (α : 𝕜) (m n : ℤ) :
    (chargedFockVirasoroMode 𝕜 α m).commutator
        (chargedFockVirasoroMode 𝕜 α n) =
      (m - n) • chargedFockVirasoroMode 𝕜 α (m + n)
        + if m + n = 0 then
            (((m ^ 3 - m : 𝕜) / (12 : 𝕜)) •
              (1 : ChargedFockCarrier 𝕜 α →ₗ[𝕜] ChargedFockCarrier 𝕜 α))
          else 0 := by
  exact CurrentHeisenbergRep.sugawaraStressMode_virasoroBracket
    (chargedFockSpaceCurrentHeisenbergRep 𝕜 α) m n

/-- A finite-stage braid system acting on the concrete charged Fock carrier. -/
structure CompatibleChargedFockAction
    (𝕜 : Type*) [Field 𝕜] [CharZero 𝕜]
    (α : 𝕜) (B : BraidGroupDiagram) where
  action :
    CompatibleStageAction 𝕜 (ChargedFockCarrier 𝕜 α) B
  modes_are_sugawara :
    action.L = chargedFockVirasoroMode 𝕜 α

namespace CompatibleChargedFockAction

variable {𝕜 : Type*} [Field 𝕜] [CharZero 𝕜]
variable {α : 𝕜} {B : BraidGroupDiagram}
variable (A : CompatibleChargedFockAction 𝕜 α B)

/-- The finite-stage charged-Fock braid action descends to the existing
categorical braid colimit. -/
abbrev descended :
    BraidGroupColimit B ⟶
      Grp.of (LinearAut 𝕜 (ChargedFockCarrier 𝕜 α)) :=
  A.action.descendedAction

/-- Universal stage restriction for the charged-Fock action. -/
theorem action_stage (n : ℕ) (b : B.obj n) :
    action A.action (stageInjection B n b) =
      A.action.stages.app n b :=
  A.action.action_stage n b

/-- Every finite-stage braid operator commutes with the existing charged-Fock
Sugawara mode. -/
theorem stage_intertwines (n : ℕ) (b : B.obj n) (m : ℤ) :
    Commute
      ((A.action.stages.app n b :
        LinearAut 𝕜 (ChargedFockCarrier 𝕜 α)) :
        ChargedFockCarrier 𝕜 α →ₗ[𝕜] ChargedFockCarrier 𝕜 α)
      (chargedFockVirasoroMode 𝕜 α m) := by
  rw [← A.modes_are_sugawara]
  exact A.action.stage_intertwines n b m

/-- The descended map is a group representation of B-infinity on the
charged Fock carrier. -/
theorem descended_mul (b c : BraidGroupColimit B) :
    A.descended b c =
      A.descended b * A.descended c := by
  exact A.action.action_mul b c

end CompatibleChargedFockAction

end InfoGeometry.Categorical.ChargedFockBraidVirasoroBridge
