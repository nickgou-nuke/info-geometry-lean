/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Lie.CanonicalZornRegularNorm
import InfoGeometry.Lie.SplitOctonionWittPairingTransportBridge
import Mathlib.LinearAlgebra.Determinant
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Exact determinant of the canonical Zorn left action

This owner uses the existing Cartesian basis obtained
from `canonicalToCoord`. The ordered coordinates of a state are
`(a, x₀, x₁, x₂, b, y₀, y₁, y₂)`.

The matrix readout is proved from the existing operator and basis. Its sparse
determinant is expanded one size at a time, removing zero branches before
expanding the next size. Basis independence then gives the exact fourth
power of the existing reduced norm in every eight-element basis.
-/

noncomputable section

namespace InfoGeometry.Lie.CanonicalZornRegularExactDet

open InfoGeometry.Canonical
open InfoGeometry.Canonical.ZornClifford
open InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis
open InfoGeometry.Lie.SplitOctonionWittPairingTransportBridge

/-- The actual left regular matrix in the existing Cartesian coordinate
order `(a, x₀, x₁, x₂, b, y₀, y₁, y₂)`. -/
theorem leftRegular_cartesian_matrix (Z : ZornMatrix ℝ) :
    LinearMap.toMatrix
        ((Pi.basisFun ℝ (Fin 8)).map canonicalToCoord.symm)
        ((Pi.basisFun ℝ (Fin 8)).map canonicalToCoord.symm)
        (leftRegularRepresentation Z) =
      !![Z.a, 0, 0, 0, 0, Z.x 0, Z.x 1, Z.x 2;
         0, Z.a, 0, 0, Z.x 0, 0, Z.y 2, -Z.y 1;
         0, 0, Z.a, 0, Z.x 1, -Z.y 2, 0, Z.y 0;
         0, 0, 0, Z.a, Z.x 2, Z.y 1, -Z.y 0, 0;
         0, Z.y 0, Z.y 1, Z.y 2, Z.b, 0, 0, 0;
         Z.y 0, 0, -Z.x 2, Z.x 1, 0, Z.b, 0, 0;
         Z.y 1, Z.x 2, 0, -Z.x 0, 0, 0, Z.b, 0;
         Z.y 2, -Z.x 1, Z.x 0, 0, 0, 0, 0, Z.b] := by
  rw [LinearMap.toMatrix_map_left, LinearMap.toMatrix_map_right]
  ext i j
  rw [LinearMap.toMatrix_apply, Pi.basisFun_apply, Pi.basisFun_repr]
  fin_cases i <;> fin_cases j <;>
    norm_num [LinearMap.comp_apply, canonicalToCoord,
      leftRegularRepresentation, leftMultiplication, ZornMatrix.mul,
      ZornMatrix.dot, ZornMatrix.cross, Pi.single_apply]

set_option maxHeartbeats 1200000 in
/-- The determinant of the eight-dimensional left action is the fourth
power of the native reduced norm, including on the null cone. -/
theorem det_leftRegular_eq_norm_pow_four
    (b : Module.Basis (Fin 8) ℝ (ZornMatrix ℝ)) (Z : ZornMatrix ℝ) :
    Matrix.det (LinearMap.toMatrix b b (leftRegularRepresentation Z)) =
      zornNormFun Z ^ 4 := by
  rw [LinearMap.det_toMatrix_eq_det_toMatrix b
    ((Pi.basisFun ℝ (Fin 8)).map canonicalToCoord.symm)
    (leftRegularRepresentation Z), leftRegular_cartesian_matrix]
  norm_num [Matrix.det_succ_row_zero (n := 7), Fin.sum_univ_succ,
    Matrix.submatrix_apply, Fin.succAbove]
  norm_num [Matrix.det_succ_row_zero (n := 6), Fin.sum_univ_succ,
    Matrix.submatrix_apply, Fin.succAbove]
  norm_num [Matrix.det_succ_row_zero (n := 5), Fin.sum_univ_succ,
    Matrix.submatrix_apply, Fin.succAbove]
  norm_num [Matrix.det_succ_row_zero (n := 4), Fin.sum_univ_succ,
    Matrix.submatrix_apply, Fin.succAbove]
  norm_num [Matrix.det_succ_row_zero (n := 3), Fin.sum_univ_succ,
    Matrix.submatrix_apply, Fin.succAbove]
  norm_num [Matrix.det_succ_row_zero (n := 2), Fin.sum_univ_succ,
    Matrix.submatrix_apply, Fin.succAbove]
  norm_num [Matrix.det_fin_two, Matrix.submatrix_apply, Fin.succAbove,
    zornNormFun, ZornMatrix.dot]
  ring

end InfoGeometry.Lie.CanonicalZornRegularExactDet
