import InfoGeometry.GrandUnification.AmplituhedronTwistorPluckerDictionary
import Mathlib.Data.Matrix.Basic
import Mathlib.Algebra.Group.Basic
import Mathlib.Tactic

/-!
# Linear Maps Preserve Decomposable Two-Blades

This module treats the two rows of `PlabicTwistorMatrix` as vectors in a
four-dimensional module. Their six 2-by-2 minors form a decomposable
two-vector and therefore satisfy the Klein quadric equation. A common linear
map on both rows again gives two vectors, so their minors still satisfy that
equation.

The result is purely algebraic: `TwistorLinearMap` is an arbitrary matrix over
a commutative ring. This file does not define SU(2,2), its Hermitian form, a
group action, a conformal spacetime, or a physical causal relation.
-/

namespace InfoGeometry.GrandUnification

open InfoGeometry.Canonical.AmplituhedronMetriplecticBridge

variable {R : Type*} [CommRing R]

/-- A linear map on the four coordinates of each row twistor. -/
def TwistorLinearMap (R : Type*) := Matrix (Fin 4) (Fin 4) R

/-- Apply the same coordinate linear map to both rows. -/
def applyTwistorLinearMap (g : TwistorLinearMap R) (Z : PlabicTwistorMatrix R) : PlabicTwistorMatrix R :=
  let z1 := fun j => g 0 j * Z.z11 + g 1 j * Z.z12 + g 2 j * Z.z13 + g 3 j * Z.z14
  let z2 := fun j => g 0 j * Z.z21 + g 1 j * Z.z22 + g 2 j * Z.z23 + g 3 j * Z.z24
  { z11 := z1 0, z12 := z1 1, z13 := z1 2, z14 := z1 3,
    z21 := z2 0, z22 := z2 1, z23 := z2 2, z24 := z2 3 }

/-- The minors of the two mapped rows satisfy the Klein quadric equation. -/
theorem linear_map_preserves_plucker_relation (g : TwistorLinearMap R) (Z : PlabicTwistorMatrix R) :
    IsKleinNull (extractOnShellTwistorBlade (applyTwistorLinearMap g Z)) := by
  dsimp [IsKleinNull, kleinQuadricEval, extractOnShellTwistorBlade, applyTwistorLinearMap]
  ring

end InfoGeometry.GrandUnification
