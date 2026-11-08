/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Canonical.OperatorLogDetDikinGeometry
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# Exact native logdet derivatives in a noncommuting matrix direction

The base point `!![2, 1; 1, 2]` is strictly positive, and the Hermitian
direction `(1 / 4) • !![1, 1; 1, -1]` does not commute with it. The calculations
below use the actual matrix inverse and actual native derivatives. The final
positivity conclusion is obtained from the proved native Dikin theorem.
-/

noncomputable section

namespace InfoGeometry.Canonical.OperatorLogDetDikinGeometryTests

open InfoGeometry.Analysis.ComplexMatrixLogDetCalculus
open InfoGeometry.Analysis.PositiveMatrixDikin
open InfoGeometry.Canonical.OperatorLogDetDikinGeometry
open InfoGeometry.Canonical.PolarFrameTraceDensity
open InfoGeometry.Geometry.LegendreDifferential
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator

abbrev TestMatrix := Matrix (Fin 2) (Fin 2) ℂ

def baseMatrix : TestMatrix := !![2, 1; 1, 2]

def directionMatrix : TestMatrix := (1 / 4 : ℂ) • !![1, 1; 1, -1]

def gramFactor : TestMatrix := !![1, 1; 0, 0]

def inverseBaseMatrix : TestMatrix := (1 / 3 : ℂ) • !![2, -1; -1, 2]

/-- The positive remainder is an actual matrix Gram product. -/
theorem baseMatrix_sub_one_eq_star_mul_self :
    baseMatrix - 1 = star gramFactor * gramFactor := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [baseMatrix, gramFactor, Matrix.star_apply, Matrix.mul_apply,
      Fin.sum_univ_two]

/-- Strict positivity follows from the operator-order comparison with the identity. -/
theorem baseMatrix_isStrictlyPositive : IsStrictlyPositive baseMatrix := by
  have hnonneg : 0 ≤ baseMatrix - 1 := by
    rw [baseMatrix_sub_one_eq_star_mul_self]
    exact star_mul_self_nonneg gramFactor
  exact (isStrictlyPositive_one : IsStrictlyPositive (1 : TestMatrix)).of_le
    (sub_nonneg.mp hnonneg)

/-- The tangent direction belongs to the full Hermitian matrix carrier. -/
theorem directionMatrix_isSelfAdjoint : IsSelfAdjoint directionMatrix := by
  change star directionMatrix = directionMatrix
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [directionMatrix, Matrix.star_apply, Matrix.smul_apply, smul_eq_mul]

/-- The base point and its direction do not commute, as witnessed by one entry. -/
theorem baseMatrix_directionMatrix_not_commute :
    ¬ Commute baseMatrix directionMatrix := by
  intro hcomm
  have hentry := congrArg (fun M : TestMatrix => M 0 1) hcomm.eq
  norm_num [baseMatrix, directionMatrix, Matrix.mul_apply, Fin.sum_univ_two,
    Matrix.smul_apply, smul_eq_mul] at hentry

/-- The same witness stated directly as unequal products in the matrix carrier. -/
theorem baseMatrix_directionMatrix_product_ne :
    baseMatrix * directionMatrix ≠ directionMatrix * baseMatrix := by
  intro h
  have hentry := congrArg (fun M : TestMatrix => M 0 1) h
  norm_num [baseMatrix, directionMatrix, Matrix.mul_apply, Fin.sum_univ_two,
    Matrix.smul_apply, smul_eq_mul] at hentry

/-- The displayed matrix is a genuine right inverse. -/
theorem baseMatrix_mul_inverseBaseMatrix : baseMatrix * inverseBaseMatrix = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [baseMatrix, inverseBaseMatrix, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.smul_apply, smul_eq_mul]

/-- The numerical certificate identifies the native nonsingular inverse. -/
theorem baseMatrix_inv : baseMatrix⁻¹ = inverseBaseMatrix :=
  Matrix.inv_eq_right_inv baseMatrix_mul_inverseBaseMatrix

/-- The ordered inverse variation is computed without interchanging its factors. -/
theorem baseMatrix_inv_mul_directionMatrix :
    baseMatrix⁻¹ * directionMatrix = (1 / 12 : ℂ) • !![1, 3; 1, -3] := by
  rw [baseMatrix_inv]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [inverseBaseMatrix, directionMatrix, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.smul_apply, smul_eq_mul]

/-- The actual native Fréchet Hessian has the exact value `1 / 9`. -/
theorem native_hessian_eq_one_ninth :
    hessianMap negLogDet baseMatrix directionMatrix directionMatrix = (1 / 9 : ℝ) := by
  rw [hessianMap_negLogDet_self baseMatrix directionMatrix
    baseMatrix_isStrictlyPositive.isUnit]
  rw [traceQuadratic, baseMatrix_inv_mul_directionMatrix]
  norm_num [reTrace, pow_two, Matrix.trace, Matrix.mul_apply, Fin.sum_univ_two,
    Matrix.smul_apply, smul_eq_mul]

/-- The actual third line derivative has the exact positive value `11 / 216`. -/
theorem native_third_deriv_eq_eleven_over_two_sixteen :
    deriv (deriv (deriv (fun t : ℝ => negLogDet (baseMatrix + t • directionMatrix)))) 0 =
      (11 / 216 : ℝ) := by
  rw [third_deriv_negLogDet_add_smul_zero baseMatrix directionMatrix
    baseMatrix_isStrictlyPositive.isUnit, baseMatrix_inv_mul_directionMatrix]
  norm_num [pow_succ, Matrix.trace, Matrix.mul_apply, Fin.sum_univ_two,
    Matrix.smul_apply, smul_eq_mul]

/-- The native Hessian unit bound proves positivity of the noncommuting perturbation. -/
theorem baseMatrix_add_directionMatrix_isStrictlyPositive :
    IsStrictlyPositive (baseMatrix + directionMatrix) := by
  apply native_logDet_dikin_containment baseMatrix_isStrictlyPositive
    directionMatrix_isSelfAdjoint
  rw [native_hessian_eq_one_ninth]
  norm_num

/-- Trace normalization preserves the negative-log commutator for this same full pair. -/
theorem normalized_surprisal_commutator_eq :
    (-CFC.log (normalizedDensity baseMatrix)) * directionMatrix -
        directionMatrix * (-CFC.log (normalizedDensity baseMatrix)) =
      (-CFC.log baseMatrix) * directionMatrix - directionMatrix * (-CFC.log baseMatrix) :=
  neg_log_normalizedDensity_commutator baseMatrix directionMatrix
    baseMatrix_isStrictlyPositive

end InfoGeometry.Canonical.OperatorLogDetDikinGeometryTests
