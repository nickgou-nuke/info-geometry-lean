import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.GeometricCalculusFreudenthalBridge

/-!
# InfoGeometry/Canonical/OperatorFreudenthalBoundary.lean

Bridge between geometric Stokes boundary flux and Freudenthal charge horizons.

This file does not assert that every Stokes flux computes a black-hole entropy.
Instead, it defines the proof-carrying interface that downstream modules must
instantiate once the concrete Clifford/Stokes/Freudenthal analytic layer exists.
-/

/-!
Compatibility note: the old experimental declarations have been retired.
Use `InfoGeometry.Canonical.GeometricCalculusFreudenthalBridge`, whose active
API is based on `CliffordResolventFamily`, `DirectedBoundary P`, and the
constructive theorem
`operatorFreudenthalBoundaryFluxBridge_from_witnesses`.
-/
