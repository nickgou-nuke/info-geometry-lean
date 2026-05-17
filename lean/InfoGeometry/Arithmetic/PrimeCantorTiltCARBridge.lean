import Mathlib
import InfoGeometry.Arithmetic.PrimeCantorTiltFockRepresentation
import InfoGeometry.Arithmetic.PrimeBooleanCubeCARBridge
import InfoGeometry.Arithmetic.PrimeMajoranaCAR
import InfoGeometry.Arithmetic.PrimeWittenCharacter
import InfoGeometry.Meta.BridgeTarget

/-!
# InfoGeometry.Arithmetic.PrimeCantorTiltCARBridge

Normalized Cantor tilt/switch bridge for the finite arithmetic carrier lane.

This file does not invent a new representation. It makes the existing finite
owner surfaces graph-visible in the normalized order:

* finite tilt/switch atom;
* split-Majorana local CAR atom;
* finite Boolean-cube / Möbius readout;
* finite Witten character.

No infinite Cantor/Fock equivalence.
No CCR claim.
No analytic continuation.
No Hilbert-Polya/RH claim.
-/

noncomputable section

namespace InfoGeometry.Arithmetic.PrimeCantorTiltCARBridge

/--
The normalized Cantor tilt/switch bridge target.

This is intentionally a conjunction of the existing finite owner targets:
the normalized tilt/switch atom, the split-Majorana local CAR atom, the
finite Boolean-cube bridge, and the finite Witten owner.
-/
@[bridge_target_tag]
def PrimeCantorTiltCARBridgeTarget : Prop :=
  InfoGeometry.Arithmetic.PrimeCantorTiltFockRepresentation
      .PrimeCantorTiltFockRepresentationOwnerTarget ∧
  InfoGeometry.Arithmetic.PrimeMajoranaCAR.PrimeMajoranaCAROwnerTarget ∧
  InfoGeometry.Arithmetic.PrimeBooleanCubeCARBridge
      .PrimeBooleanCubeCARBridgeOwnerTarget ∧
  InfoGeometry.Arithmetic.PrimeWittenCharacter.PrimeWittenCharacterOwnerTarget

namespace PrimeCantorTiltCARBridgeTarget

theorem normalized_tilt_switch_owner :
    InfoGeometry.Arithmetic.PrimeCantorTiltFockRepresentation
        .PrimeCantorTiltFockRepresentationOwnerTarget :=
  InfoGeometry.Arithmetic.PrimeCantorTiltFockRepresentation
    .primeCantorTiltFockRepresentationOwnerTarget

theorem split_majorana_owner :
    InfoGeometry.Arithmetic.PrimeMajoranaCAR.PrimeMajoranaCAROwnerTarget :=
  InfoGeometry.Arithmetic.PrimeMajoranaCAR.primeMajoranaCAROwnerTarget

theorem boolean_cube_car_owner :
    InfoGeometry.Arithmetic.PrimeBooleanCubeCARBridge
        .PrimeBooleanCubeCARBridgeOwnerTarget :=
  InfoGeometry.Arithmetic.PrimeBooleanCubeCARBridge
    .primeBooleanCubeCARBridgeOwnerTarget

theorem finite_witten_owner :
    InfoGeometry.Arithmetic.PrimeWittenCharacter.PrimeWittenCharacterOwnerTarget :=
  InfoGeometry.Arithmetic.PrimeWittenCharacter.primeWittenCharacterOwnerTarget

end PrimeCantorTiltCARBridgeTarget

/--
The normalized Cantor tilt/switch bridge target is closed.
-/
theorem primeCantorTiltCARBridgeTarget :
    PrimeCantorTiltCARBridgeTarget := by
  exact
    ⟨ InfoGeometry.Arithmetic.PrimeCantorTiltFockRepresentation
        .primeCantorTiltFockRepresentationOwnerTarget,
      InfoGeometry.Arithmetic.PrimeMajoranaCAR.primeMajoranaCAROwnerTarget,
      InfoGeometry.Arithmetic.PrimeBooleanCubeCARBridge
        .primeBooleanCubeCARBridgeOwnerTarget,
      InfoGeometry.Arithmetic.PrimeWittenCharacter.primeWittenCharacterOwnerTarget ⟩

end InfoGeometry.Arithmetic.PrimeCantorTiltCARBridge
