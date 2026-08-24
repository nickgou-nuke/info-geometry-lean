/- SPDX-License-Identifier: Apache-2.0 -/

import InfoGeometry.Exceptional.G2ThreePlaneWeightBridge
import InfoGeometry.Algebra.Zorn.G2PositiveRootCoordinateBridge
import InfoGeometry.Algebra.ZornMatrix
import InfoGeometry.Canonical.ZornVectorMatrixExplicit

/-!
# Coordinate-level compatibility for the three-plane packet

This file records only the finite coordinate identities needed for a future
intertwiner.  It does not identify Zorn multiplication with a Lie bracket or
with braid composition.
-/

namespace InfoGeometry.Exceptional.G2ThreePlaneRootCoordinateBridge

open InfoGeometry.Algebra.Zorn.G2PositiveRootCoordinateBridge
open InfoGeometry.Exceptional.G2ThreePlaneWeightBridge
open InfoGeometry.Canonical.ZornVectorMatrixExplicit

theorem short_root_coordinate_addition_01 :
    (rootCoordinates (shortRoot 0)).1 +
        (rootCoordinates (shortRoot 1)).1 =
      (rootCoordinates (shortRoot 2)).1 ∧
    (rootCoordinates (shortRoot 0)).2 +
        (rootCoordinates (shortRoot 1)).2 =
      (rootCoordinates (shortRoot 2)).2 := by
  norm_num [shortRoot, rootCoordinates]

theorem short_root_coordinate_addition_10 :
    (rootCoordinates (shortRoot 1)).1 +
        (rootCoordinates (shortRoot 0)).1 =
      (rootCoordinates (shortRoot 2)).1 ∧
    (rootCoordinates (shortRoot 1)).2 +
        (rootCoordinates (shortRoot 0)).2 =
      (rootCoordinates (shortRoot 2)).2 := by
  norm_num [shortRoot, rootCoordinates]

theorem zorn_cross_basis_01 :
    cross3 (InfoGeometry.Algebra.ZornMatrix.Vec3.basis 0)
        (InfoGeometry.Algebra.ZornMatrix.Vec3.basis 1) =
      InfoGeometry.Algebra.ZornMatrix.Vec3.basis 2 := by
  ext k
  fin_cases k <;>
    norm_num [cross3, InfoGeometry.Algebra.ZornMatrix.Vec3.basis, Fin.ext_iff]

theorem zorn_cross_basis_10 :
    cross3 (InfoGeometry.Algebra.ZornMatrix.Vec3.basis 1)
        (InfoGeometry.Algebra.ZornMatrix.Vec3.basis 0) =
      -(InfoGeometry.Algebra.ZornMatrix.Vec3.basis 2) := by
  ext k
  fin_cases k <;>
    norm_num [cross3, InfoGeometry.Algebra.ZornMatrix.Vec3.basis, Fin.ext_iff]

end InfoGeometry.Exceptional.G2ThreePlaneRootCoordinateBridge
