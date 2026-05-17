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
The normalized Cantor tilt/switch bridge targets.

These are thin bridge reexports of the existing finite owner surfaces:
the normalized tilt/switch atom, the split-Majorana local CAR atom,
the finite Boolean-cube bridge, and the finite Witten owner.
-/
@[bridge_target_tag]
theorem primeCantorTiltFockRepresentationOwnerTarget_bridge :
    InfoGeometry.Arithmetic.PrimeCantorTiltFockRepresentation.PrimeCantorTiltFockRepresentationOwnerTarget :=
  InfoGeometry.Arithmetic.PrimeCantorTiltFockRepresentation.primeCantorTiltFockRepresentationOwnerTarget

@[bridge_target_tag]
theorem primeMajoranaCAROwnerTarget_bridge :
    InfoGeometry.Arithmetic.PrimeMajoranaCAR.ExteriorCARPair.PrimeMajoranaCAROwnerTarget :=
  InfoGeometry.Arithmetic.PrimeMajoranaCAR.ExteriorCARPair.primeMajoranaCAROwnerTarget

@[bridge_target_tag]
theorem primeBooleanCubeCARBridgeOwnerTarget_bridge :
    InfoGeometry.Arithmetic.PrimeBooleanCubeCARBridge.PrimeBooleanCubeCARBridgeOwnerTarget :=
  InfoGeometry.Arithmetic.PrimeBooleanCubeCARBridge.primeBooleanCubeCARBridgeOwnerTarget

@[bridge_target_tag]
theorem primeWittenCharacterOwnerTarget_bridge :
    InfoGeometry.Arithmetic.PrimeWittenCharacter.PrimeWittenCharacterOwnerTarget :=
  InfoGeometry.Arithmetic.PrimeWittenCharacter.primeWittenCharacterOwnerTarget

end InfoGeometry.Arithmetic.PrimeCantorTiltCARBridge
