/- SPDX-License-Identifier: Apache-2.0 -/

/-
# Categorical braid action on a Virasoro carrier

This is the concrete categorical action interface missing between the existing
finite braid colimit and the existing Clifford/Sugawara/Virasoro carriers.
Finite-stage representations are supplied as a compatible representation
cocone into the group of linear automorphisms of one carrier.  Mathlib's group
colimit universal property then constructs the B-infinity action.

No finite braid representation is invented here, and no identification between
the Hestenes--Krein carrier and the Virasoro carrier is asserted.
-/

import InfoGeometry.Categorical.BraidHestenesKreinVirasoroBridge
import InfoGeometry.Categorical.BraidVirasoroIntertwiner

noncomputable section

namespace InfoGeometry.Categorical.BraidColimitVirasoroAction

open CategoryTheory
open InfoGeometry.Categorical.HadjiivanovBraidGroupColimit
open InfoGeometry.Categorical.BraidHestenesKreinVirasoroBridge
open InfoGeometry.Categorical.BraidVirasoroIntertwiner

universe u

/-- The group of linear automorphisms of a carrier. -/
abbrev LinearAut (𝕜 V : Type u) [CommRing 𝕜]
    [AddCommGroup V] [Module 𝕜 V] :=
  V ≃ₗ[𝕜] V

/-- A compatible family of finite-stage braid representations. -/
structure CompatibleStageAction
    (𝕜 V : Type u) [CommRing 𝕜]
    [AddCommGroup V] [Module 𝕜 V]
    (B : BraidGroupDiagram.{u}) where
  L : ℤ → Module.End 𝕜 V
  stages :
    RepresentationCocone B (Grp.of (LinearAut 𝕜 V))
  stage_intertwines :
    ∀ (n : ℕ) (b : B.obj n) (m : ℤ),
      Commute
        ((stages.app n b : LinearAut 𝕜 V) : V →ₗ[𝕜] V)
        (L m)

/-- The categorical action of the braid colimit on the carrier. -/
abbrev descendedAction
    {𝕜 V : Type u} [CommRing 𝕜]
    [AddCommGroup V] [Module 𝕜 V]
    {B : BraidGroupDiagram.{u}}
    (A : CompatibleStageAction 𝕜 V B) :
    BraidGroupColimit B ⟶ Grp.of (LinearAut 𝕜 V) :=
  descendedRepresentation B (Grp.of (LinearAut 𝕜 V)) A.stages

/-- Pointwise form of the descended B-infinity action. -/
def action
    {𝕜 V : Type u} [CommRing 𝕜]
    [AddCommGroup V] [Module 𝕜 V]
    {B : BraidGroupDiagram.{u}}
    (A : CompatibleStageAction 𝕜 V B)
    (b : BraidGroupColimit B) : LinearAut 𝕜 V :=
  A.descendedAction b

namespace CompatibleStageAction

variable {𝕜 V : Type u} [CommRing 𝕜]
variable [AddCommGroup V] [Module 𝕜 V]
variable {B : BraidGroupDiagram.{u}}
variable (A : CompatibleStageAction 𝕜 V B)

/-- The descended action restricts to the supplied action at every finite
stage. -/
theorem action_stage
    (n : ℕ) (b : B.obj n) :
    action A (stageInjection B n b) = A.stages.app n b := by
  exact congrArg (fun f => f b)
    (stageInjection_descendedRepresentation B
      (Grp.of (LinearAut 𝕜 V)) A.stages n)

/-- Every finite-stage action commutes with every Virasoro mode. -/
theorem stage_intertwines
    (n : ℕ) (b : B.obj n) (m : ℤ) :
    Commute
      ((A.stages.app n b : LinearAut 𝕜 V) : V →ₗ[𝕜] V)
      (A.L m) :=
  A.stage_intertwines n b m

/-- The universal representation law for the descended action. -/
theorem action_mul
    (b c : BraidGroupColimit B) :
    action A (b * c) = action A b * action A c := by
  exact map_mul A.descendedAction b c

/-- The descended action is the unique group homomorphism having the supplied
finite-stage restrictions. -/
theorem action_unique
    (f : BraidGroupColimit B ⟶ Grp.of (LinearAut 𝕜 V))
    (h : ∀ n : ℕ, ∀ b : B.obj n,
      f (stageInjection B n b) = A.stages.app n b) :
    f = A.descendedAction := by
  apply descendedRepresentation_unique B
    (Grp.of (LinearAut 𝕜 V)) A.stages f
  intro n
  ext b
  exact h n b

end CompatibleStageAction

/-- A carrier-level closure package combines any existing bridge object with
a genuine compatible finite-stage action. -/
structure CertifiedClosure
    (Bridge : Type*) (𝕜 V : Type u)
    [CommRing 𝕜] [AddCommGroup V] [Module 𝕜 V]
    (B : BraidGroupDiagram.{u})
    (L : ℤ → Module.End 𝕜 V) where
  bridge : Bridge
  action : CompatibleStageAction 𝕜 V B
  modes : action.L = L

/-- Attach a concrete compatible stage action to an existing bridge packet. -/
def attach
    {Bridge : Type*} {𝕜 V : Type u}
    [CommRing 𝕜] [AddCommGroup V] [Module 𝕜 V]
    {B : BraidGroupDiagram.{u}}
    {L : ℤ → Module.End 𝕜 V}
    (bridge : Bridge)
    (A : CompatibleStageAction 𝕜 V B)
    (hL : A.L = L) :
    CertifiedClosure Bridge 𝕜 V B L :=
  ⟨bridge, A, hL⟩

end InfoGeometry.Categorical.BraidColimitVirasoroAction
