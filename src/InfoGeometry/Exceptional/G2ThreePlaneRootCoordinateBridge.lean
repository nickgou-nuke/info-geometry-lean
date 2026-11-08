/- SPDX-License-Identifier: Apache-2.0 -/

import InfoGeometry.Exceptional.G2ThreePlaneWeightBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.QuantumAlgebra.ThreePlaneChiralCarrier
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
open InfoGeometry.QuantumAlgebra.ThreePlaneChiralCarrier

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

/-! ## Exact compatibility on the first oriented pair -/

theorem upper_chiral_product_01_matches_lower_2 :
    zornMul (upperChiralBasis 0) (upperChiralBasis 1) =
      lowerChiralBasis 2 := by
  rw [upperChiralBasis_mul_upperChiralBasis]
  rw [zorn_cross_basis_01]
  rfl

theorem lower_chiral_product_01_matches_negative_upper_2 :
    zornMul (lowerChiralBasis 0) (lowerChiralBasis 1) =
      -upperChiralBasis 2 := by
  rw [lowerChiralBasis_mul_lowerChiralBasis]
  rw [zorn_cross_basis_01]
  ext <;>
    simp [upperChiralBasis, upperVectorZorn, zornMk,
      InfoGeometry.Algebra.ZornMatrix.Vec3.basis]

theorem upper_chiral_product_10_matches_negative_lower_2 :
    zornMul (upperChiralBasis 1) (upperChiralBasis 0) =
      -lowerChiralBasis 2 := by
  rw [upperChiralBasis_mul_upperChiralBasis]
  rw [zorn_cross_basis_10]
  ext <;>
    simp [lowerChiralBasis, lowerVectorZorn, zornMk,
      InfoGeometry.Algebra.ZornMatrix.Vec3.basis]

theorem lower_chiral_product_10_matches_upper_2 :
    zornMul (lowerChiralBasis 1) (lowerChiralBasis 0) =
      upperChiralBasis 2 := by
  rw [lowerChiralBasis_mul_lowerChiralBasis]
  rw [zorn_cross_basis_10]
  ext <;>
    simp [upperChiralBasis, upperVectorZorn, zornMk,
      InfoGeometry.Algebra.ZornMatrix.Vec3.basis]

end InfoGeometry.Exceptional.G2ThreePlaneRootCoordinateBridge
