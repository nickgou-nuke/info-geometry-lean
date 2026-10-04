import InfoGeometry.GrandUnification.AmplituhedronTwistorPluckerDictionary
import Mathlib.Tactic

/-!
# A Coordinate Shear Preserves the Klein Quadric Identity

This module proves a polynomial identity for a specified shear of one coordinate
of the two-row matrix. The resulting minors satisfy the Klein quadric equation,
as they are the minors of two vectors. This is an algebraic statement only: the
file does not define BCFW recursion, momentum-space shifts, amplitudes, or
SU(2,2).
-/

namespace InfoGeometry.GrandUnification

open InfoGeometry.Canonical.AmplituhedronMetriplecticBridge

variable {R : Type*} [CommRing R] [LinearOrder R]

/-- 
The coordinate shear adds `z` times the first coordinate to the second
coordinate in each row.
-/
def applyCoordinateShear (Z : PlabicTwistorMatrix R) (z : R) : PlabicTwistorMatrix R :=
  { z11 := Z.z11, z12 := Z.z12 + z * Z.z11, z13 := Z.z13, z14 := Z.z14,
    z21 := Z.z21, z22 := Z.z22 + z * Z.z21, z23 := Z.z23, z24 := Z.z24 }

/-- 
The sheared rows still define a decomposable two-vector.
-/
theorem coordinate_shear_preserves_plucker_relation (Z : PlabicTwistorMatrix R) (z : R) :
    IsKleinNull (extractOnShellTwistorBlade (applyCoordinateShear Z z)) := by
  dsimp [IsKleinNull, kleinQuadricEval, extractOnShellTwistorBlade, applyCoordinateShear]
  ring

end InfoGeometry.GrandUnification
