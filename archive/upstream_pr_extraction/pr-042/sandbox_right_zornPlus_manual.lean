import Mathlib.Data.Matrix.Basic
import InfoGeometry.Lie.SplitOctonionCircularPeirceBasis
import InfoGeometry.Lie.SplitOctonionCircularOperatorReadout

open InfoGeometry.Lie.SplitOctonionCircularOperatorReadout
open InfoGeometry.Algebra.Zorn.SplitQuaternionCore
open InfoGeometry.Lie.SplitOctonionQuaternionZornCoordinates

theorem test_right_zornPlus_0_0 (i j : Fin 8) :
    R_mat zornPlus i j = Matrix.diagonal (fun k : Fin 8 => if k.val = 0 then 1 else if k.val < 5 then 0 else (1:ℝ)) i j := by
  fin_cases i <;> fin_cases j <;> (
    dsimp [R_mat, circularMatrix, LinearMap.toMatrixAlgEquiv_apply, LinearMap.toMatrix_apply,
      Pi.basisFun_apply, Matrix.diagonal_apply, circularR_apply]
    rw [circularCoordinateLinearEquiv_symm_single]
    change circularCoordinateLinearEquiv (circularPeirceBasis _ * zornPlus) _ = _
    rw [circularPeirceBasis_mul_zornPlus]
    simp [-circularPeirceBasis_apply, equivFun_basis]
  )
