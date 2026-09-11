import InfoGeometry.Canonical.GeometricCalculusFreudenthalBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# InfoGeometry/Canonical/GeometricFreudenthalBoundary.lean

Structural bridge between real Clifford/Stokes boundary flux and the
Freudenthal charge horizon.

This file does not assert that the geometric flux theorem has been proved.
It provides the witness interface by which a scalar readout of the Stokes
flux projector may be identified with the Freudenthal quartic invariant.
-/

/-!
Compatibility note: the old experimental declarations have been retired.
Use `InfoGeometry.Canonical.GeometricCalculusFreudenthalBridge`, whose active
API keeps the Stokes/Freudenthal identification witness-gated and provides
`operatorFreudenthalBoundaryFluxBridge_from_witnesses` for constructive
packaging.
-/
