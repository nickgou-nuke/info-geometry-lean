/- SPDX-License-Identifier: Apache-2.0 -/

import InfoGeometry.Canonical.WheelerItFromBit
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Wheeler's `it from bit` compatibility path

The canonical owner is `InfoGeometry.Canonical.WheelerItFromBit`; this module
preserves the upstream namespace without duplicating its proofs.
-/

namespace InfoGeometry.Physics.WheelerItFromBit

abbrev Spinor32 := InfoGeometry.Canonical.WheelerItFromBit.Spinor32
abbrev Mat32 := InfoGeometry.Canonical.WheelerItFromBit.Mat32
abbrev QuantumBit := InfoGeometry.Canonical.WheelerItFromBit.QuantumBit
abbrev itFromBitCoordinate := InfoGeometry.Canonical.WheelerItFromBit.itFromBitCoordinate
abbrev emergentGravitationalMetric :=
  InfoGeometry.Canonical.WheelerItFromBit.emergentGravitationalMetric

theorem it_vanishes_for_zero_state (A : Mat32) :
    itFromBitCoordinate 0 A = 0 :=
  InfoGeometry.Canonical.WheelerItFromBit.it_vanishes_for_zero_state A

theorem emergentGravitationalMetric_comm_symm
    (rho A B : Mat32) (h_comm : A * B = B * A) :
    emergentGravitationalMetric rho A B =
      emergentGravitationalMetric rho B A :=
  InfoGeometry.Canonical.WheelerItFromBit.emergentGravitationalMetric_comm_symm
    rho A B h_comm

end InfoGeometry.Physics.WheelerItFromBit
