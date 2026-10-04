import InfoGeometry.Canonical.AmplituhedronMetriplecticBridge
import InfoGeometry.Canonical.NativeMathlibAmplituhedronBridge
import Mathlib.Tactic

/-!
# Two-Row Matrices and the Klein Quadric Equation

This module defines an arbitrary two-row, four-column matrix and its six
2-by-2 minors. The minors satisfy the Klein quadric equation because they are
the coordinates of a decomposable two-vector. No plabic graph, positivity
condition, spacetime causal relation, or amplituhedron membership is defined
here.
-/

namespace InfoGeometry.GrandUnification

open InfoGeometry.Canonical.AmplituhedronMetriplecticBridge
open InfoGeometry.Canonical.NativeMathlibAmplituhedronBridge

variable {R : Type*} [CommRing R] [LinearOrder R]

/-- An arbitrary two-row array of four coordinates over `R`. -/
structure PlabicTwistorMatrix (R : Type*) where
  z11 : R
  z12 : R
  z13 : R
  z14 : R
  z21 : R
  z22 : R
  z23 : R
  z24 : R

/-- The six 2-by-2 minors of the two rows, packaged as Plücker coordinates. -/
def extractOnShellTwistorBlade (Z : PlabicTwistorMatrix R) : KinematicPluckerPoint R :=
  { p12 := Z.z11 * Z.z22 - Z.z12 * Z.z21
    p34 := Z.z13 * Z.z24 - Z.z14 * Z.z23
    p13 := Z.z11 * Z.z23 - Z.z13 * Z.z21
    p24 := Z.z12 * Z.z24 - Z.z14 * Z.z22
    p14 := Z.z11 * Z.z24 - Z.z14 * Z.z21
    p23 := Z.z12 * Z.z23 - Z.z13 * Z.z22 }

/-- The minors of any two-row matrix satisfy the Klein quadric equation. -/
theorem extracted_blade_satisfies_klein_relation (Z : PlabicTwistorMatrix R) :
    IsKleinNull (extractOnShellTwistorBlade Z) := by
  dsimp [IsKleinNull, kleinQuadricEval, extractOnShellTwistorBlade]
  ring

end InfoGeometry.GrandUnification
