/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Section13
import InfoGeometry.Projective.KleinQuadric

/-!
# Two-qubit vectors and the Plücker line quadric

The two-qubit state carrier in `Section13` is a four-coordinate vector.  This
file gives the coordinate-preserving interpretation as a point of projective
three-space and specializes the native wedge theorem to lines spanned by two
such states.  The Plücker condition concerns the decomposable bivector
`ψ ∧ φ`; it is not a criterion for either state to be separable.  Separability
is characterized independently by `Section13.twoQubit_product_iff_concurrence_zero`.

#### BUCKET 1: CLOSED FINITE THEOREMS
The coordinate map and the Plücker polynomial identity for a pair of states
are proved over `ℂ` below.

#### BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT PREMISES
No orthogonality or nonzero hypotheses are needed for the decomposable-wedge
identity. Projective-line interpretation requires a nonzero, independent pair.

#### BUCKET 3: OPEN CLOSURE DEBT
This finite coordinate result does not identify the state carrier with a
Clifford minimal ideal, construct a scattering matrix, or prove an amplituhedron
canonical form or BCFW triangulation.
-/

namespace InfoGeometry.Twistor.TwoQubitPluckerBridge

open InfoGeometry.Projective.KleinQuadric

/-- Regard a repository two-qubit state as a point-coordinate vector in `ℂ⁴`. -/
def toProjectiveVec4 (ψ : Section13.TwoQubitVec) : Vec4 ℂ where
  x0 := ψ 0
  x1 := ψ 1
  x2 := ψ 2
  x3 := ψ 3

/-- The Plücker coordinates of the line spanned by two two-qubit vectors. -/
def stateLine (ψ φ : Section13.TwoQubitVec) : Plucker6 ℂ :=
  Vec4.wedge (toProjectiveVec4 ψ) (toProjectiveVec4 φ)

/-- The six minors of two state vectors satisfy the explicit Plücker relation.
This is the coordinate identity for a decomposable bivector; if the vectors
are nonzero and independent, it represents their projective line. -/
theorem stateLine_plucker_relation (ψ φ : Section13.TwoQubitVec) :
    (stateLine ψ φ).p01 * (stateLine ψ φ).p23 -
      (stateLine ψ φ).p02 * (stateLine ψ φ).p13 +
      (stateLine ψ φ).p03 * (stateLine ψ φ).p12 = 0 := by
  change (ψ 0 * φ 1 - ψ 1 * φ 0) * (ψ 2 * φ 3 - ψ 3 * φ 2) -
      (ψ 0 * φ 2 - ψ 2 * φ 0) * (ψ 1 * φ 3 - ψ 3 * φ 1) +
      (ψ 0 * φ 3 - ψ 3 * φ 0) * (ψ 1 * φ 2 - ψ 2 * φ 1) = 0
  ring

end InfoGeometry.Twistor.TwoQubitPluckerBridge
