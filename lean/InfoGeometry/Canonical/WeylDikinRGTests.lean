/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.RelativeDikinCoarseGraining
import InfoGeometry.Analysis.PositiveMatrixDikinCongruence
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# A noncommuting finite-matrix Dikin and coarse-graining example

One positive definite `2 × 2` complex matrix and one noncommuting Hermitian
variation have exact Dikin quadratic `1 / 9`. An invertible nonunitary shear
and simultaneous positive scaling preserve that value. The consumer theorems
then bound the actual normalized inverse by `2` and transport the radius
through a fixed `1 × 2` observation map with observation precision `1`.

The input radius is computed from the actual matrix inverse. The inverse and
coarse-graining conclusions use the new consumer API, with no supplied
positivity or inverse assumption on the perturbed base matrix.
-/

noncomputable section

namespace InfoGeometry.Canonical.WeylDikinRGTests

open Matrix
open InfoGeometry.Analysis.PositiveMatrixDikin
open InfoGeometry.Canonical.RelativeDikinCoarseGraining
open InfoGeometry.OperatorAlgebra.PositiveCoarseGraining
open scoped Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator

abbrev FineMatrix := Matrix (Fin 2) (Fin 2) ℂ
abbrev CoarseMatrix := Matrix (Fin 1) (Fin 1) ℂ

def baseMatrix : FineMatrix := !![2, 1; 1, 2]

def directionMatrix : FineMatrix := (1 / 4 : ℂ) • !![1, 1; 1, -1]

def shearMatrix : FineMatrix := !![1, 1; 0, 1]

def observationMatrix : Matrix (Fin 1) (Fin 2) ℂ := !![1, 1]

private def gramFactor : FineMatrix := !![1, 1; 0, 0]

private def inverseBaseMatrix : FineMatrix := (1 / 3 : ℂ) • !![2, -1; -1, 2]

private theorem baseMatrix_sub_one_eq_star_mul_self :
    baseMatrix - 1 = star gramFactor * gramFactor := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [baseMatrix, gramFactor, Matrix.star_apply, Matrix.mul_apply,
      Fin.sum_univ_two]

/-- The base point dominates the identity by an actual Gram product. -/
theorem baseMatrix_isStrictlyPositive : IsStrictlyPositive baseMatrix := by
  have hnonneg : 0 ≤ baseMatrix - 1 := by
    rw [baseMatrix_sub_one_eq_star_mul_self]
    exact star_mul_self_nonneg gramFactor
  exact (isStrictlyPositive_one : IsStrictlyPositive (1 : FineMatrix)).of_le
    (sub_nonneg.mp hnonneg)

theorem baseMatrix_posDef : baseMatrix.PosDef :=
  baseMatrix_isStrictlyPositive.posDef

theorem directionMatrix_isSelfAdjoint : IsSelfAdjoint directionMatrix := by
  change star directionMatrix = directionMatrix
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [directionMatrix, Matrix.star_apply, Matrix.smul_apply, smul_eq_mul]

/-- One off-diagonal entry witnesses the genuinely noncommuting input pair. -/
theorem baseMatrix_directionMatrix_product_ne :
    baseMatrix * directionMatrix ≠ directionMatrix * baseMatrix := by
  intro hcomm
  have hentry := congrArg (fun M : FineMatrix => M 0 1) hcomm
  norm_num [baseMatrix, directionMatrix, Matrix.mul_apply, Fin.sum_univ_two,
    Matrix.smul_apply, smul_eq_mul] at hentry

private theorem baseMatrix_inv : baseMatrix⁻¹ = inverseBaseMatrix := by
  apply Matrix.inv_eq_right_inv
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [baseMatrix, inverseBaseMatrix, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.smul_apply, smul_eq_mul]

private theorem baseMatrix_inv_mul_directionMatrix :
    baseMatrix⁻¹ * directionMatrix = (1 / 12 : ℂ) • !![1, 3; 1, -3] := by
  rw [baseMatrix_inv]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [inverseBaseMatrix, directionMatrix, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.smul_apply, smul_eq_mul]

/-- Exact evaluation of the ordered trace square using the native matrix inverse. -/
theorem traceQuadratic_eq_one_ninth :
    traceQuadratic baseMatrix directionMatrix = (1 / 9 : ℝ) := by
  rw [traceQuadratic, baseMatrix_inv_mul_directionMatrix]
  norm_num [reTrace, pow_two, Matrix.trace, Matrix.mul_apply, Fin.sum_univ_two,
    Matrix.smul_apply, smul_eq_mul]

theorem shearMatrix_isUnit : IsUnit shearMatrix := by
  apply (Matrix.isUnit_iff_isUnit_det shearMatrix).mpr
  norm_num [shearMatrix, Matrix.det_fin_two]

/-- The change of coordinates is outside the unitary special case. -/
theorem shearMatrix_not_unitary : shearMatrix ∉ unitary FineMatrix := by
  intro hunitary
  have hentry := congrArg (fun M : FineMatrix => M 0 0)
    (Unitary.mul_star_self_of_mem hunitary)
  norm_num [shearMatrix, Matrix.star_apply, Matrix.mul_apply, Fin.sum_univ_two]
    at hentry

/-- Congruence preserves the exact radius under the nonunitary shear. -/
theorem shear_traceQuadratic_eq_one_ninth :
    traceQuadratic (shearMatrix * baseMatrix * shearMatrixᴴ)
      (shearMatrix * directionMatrix * shearMatrixᴴ) = (1 / 9 : ℝ) := by
  rw [traceQuadratic_congr baseMatrix directionMatrix shearMatrix shearMatrix_isUnit,
    traceQuadratic_eq_one_ninth]

/-- Simultaneously scaling the base point and direction preserves the same radius. -/
theorem scaled_traceQuadratic_eq_one_ninth :
    traceQuadratic ((3 : ℝ) • baseMatrix) ((3 : ℝ) • directionMatrix) =
      (1 / 9 : ℝ) := by
  rw [traceQuadratic_smul_pos baseMatrix_isStrictlyPositive directionMatrix 3
    (by norm_num), traceQuadratic_eq_one_ninth]

theorem dikin_radius_eq_one_third :
    Real.sqrt (traceQuadratic baseMatrix directionMatrix) = (1 / 3 : ℝ) := by
  rw [traceQuadratic_eq_one_ninth]
  exact (Real.sqrt_eq_iff_eq_sq (by norm_num) (by norm_num)).mpr (by norm_num)

theorem dikin_radius_le_half :
    Real.sqrt (traceQuadratic baseMatrix directionMatrix) ≤ (1 / 2 : ℝ) := by
  rw [dikin_radius_eq_one_third]
  norm_num

/-- The computed Dikin radius bounds the actual normalized inverse. -/
theorem normalized_inverse_norm_le_two :
    ‖baseMatrix ^ (1 / 2 : ℝ) * (baseMatrix + directionMatrix)⁻¹ *
      baseMatrix ^ (1 / 2 : ℝ)‖ ≤ 2 := by
  have h := norm_normalized_inverse_le_of_dikin_radius baseMatrix_posDef
    directionMatrix_isSelfAdjoint dikin_radius_le_half
      (by norm_num : (1 / 2 : ℝ) < 1)
  norm_num at h
  exact h

/-- The same radius constructs positivity and both coarse precision bounds for
the rectangular observation map, with `R = 1` and `DR = 0`. -/
theorem rectangular_coarse_sandwich :
    (baseMatrix + directionMatrix).PosDef ∧
      (1 / 2 : ℝ) • coarsePrecision baseMatrix (1 : CoarseMatrix) observationMatrix ≤
        coarsePrecision (baseMatrix + directionMatrix) (1 : CoarseMatrix)
          observationMatrix ∧
      coarsePrecision (baseMatrix + directionMatrix) (1 : CoarseMatrix)
          observationMatrix ≤
        (3 / 2 : ℝ) • coarsePrecision baseMatrix (1 : CoarseMatrix) observationMatrix := by
  have hzero : Real.sqrt (traceQuadratic (1 : CoarseMatrix) 0) ≤ (1 / 2 : ℝ) := by
    norm_num [traceQuadratic, reTrace]
  have h := coarsePrecision_relative_sandwich_of_dikin
    (A := baseMatrix) (DA := directionMatrix) (R := (1 : CoarseMatrix))
    (DR := 0) observationMatrix baseMatrix_posDef Matrix.PosDef.one
    directionMatrix_isSelfAdjoint IsSelfAdjoint.zero
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)
    dikin_radius_le_half hzero
  refine ⟨h.1, ?_, ?_⟩
  · have hlo := h.2.2.1
    norm_num at hlo
    exact hlo
  · have hhi := h.2.2.2
    norm_num at hhi
    exact hhi

end InfoGeometry.Canonical.WeylDikinRGTests
