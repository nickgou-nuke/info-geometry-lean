/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
/- The Apache LICENSE for these contributed files is retained as
`LICENSE-InfoGeometry-Apache-2.0` at the package root, together with
`NOTICE-InfoGeometry`; the upstream root CC0 license is separate. -/
import GaussianBlockSpin.MatrixWeighted.Composition
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# A real, noncommuting matrix-weighted Gaussian example

The construction follows the Gram-plus-identity positivity witnesses of
`tests/BalabanOperatorTests.lean` in `nickgou-nuke/info-geometry-lean`.
Here both spaces have real dimension two, both precision matrices have
off-diagonal entries, and the observation is a nontrivial shear. Exact entries
of the response, covariance, and precision distinguish the order of factors.
No complexification or simultaneous diagonalization is used.
-/

noncomputable section

namespace GaussianBlockSpin.MatrixWeighted.Examples

open Matrix

def fineSeed : Matrix (Fin 2) (Fin 2) ℝ := !![1, 1; 0, 0]
def coarseSeed : Matrix (Fin 2) (Fin 2) ℝ := !![1, 1; 1, 0]
def fineMatrix : Matrix (Fin 2) (Fin 2) ℝ := 1 + fineSeedᴴ * fineSeed
def coarseWeight : Matrix (Fin 2) (Fin 2) ℝ := 1 + coarseSeedᴴ * coarseSeed
def observation : Matrix (Fin 2) (Fin 2) ℝ := !![1, 1; 0, 1]

theorem fineMatrix_posDef : fineMatrix.PosDef :=
  Matrix.PosDef.one.add_posSemidef (Matrix.posSemidef_conjTranspose_mul_self fineSeed)

theorem coarseWeight_posDef : coarseWeight.PosDef :=
  Matrix.PosDef.one.add_posSemidef (Matrix.posSemidef_conjTranspose_mul_self coarseSeed)

theorem fine_coarse_noncommuting : fineMatrix * coarseWeight ≠ coarseWeight * fineMatrix := by
  intro h
  have hentry := congrArg (fun M => M 0 1) h
  norm_num [fineMatrix, fineSeed, coarseWeight, coarseSeed, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Matrix.one_apply, Fin.sum_univ_succ] at hentry

theorem weight_transport_noncommuting :
    coarseWeight * (observation * fineMatrix * observationᴴ) ≠
      (observation * fineMatrix * observationᴴ) * coarseWeight := by
  intro h
  have hentry := congrArg (fun M => M 0 1) h
  norm_num [coarseWeight, coarseSeed, fineMatrix, fineSeed, observation, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Matrix.one_apply, Fin.sum_univ_succ] at hentry

theorem fineMatrix_inv : fineMatrix⁻¹ = !![(2 / 3 : ℝ), -1 / 3; -1 / 3, 2 / 3] := by
  apply Matrix.inv_eq_right_inv
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [fineMatrix, fineSeed, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Matrix.one_apply, Fin.sum_univ_succ]

theorem coarseWeight_inv : coarseWeight⁻¹ = !![(2 / 5 : ℝ), -1 / 5; -1 / 5, 3 / 5] := by
  apply Matrix.inv_eq_right_inv
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [coarseWeight, coarseSeed, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Matrix.one_apply, Fin.sum_univ_succ]

theorem explicit_finePrecision :
    finePrecision fineMatrix coarseWeight observation = !![(5 : ℝ), 5; 5, 9] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [finePrecision, fineMatrix, fineSeed, coarseWeight, coarseSeed, observation,
      Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply, Fin.sum_univ_succ]

theorem explicit_finePrecision_inv :
    (finePrecision fineMatrix coarseWeight observation)⁻¹ =
      !![(9 / 20 : ℝ), -1 / 4; -1 / 4, 1 / 4] := by
  rw [explicit_finePrecision]
  apply Matrix.inv_eq_right_inv
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.mul_apply, Matrix.one_apply, Fin.sum_univ_succ]

theorem explicit_harmonicExtension :
    harmonicExtension fineMatrix coarseWeight observation =
      !![(7 / 20 : ℝ), -3 / 10; 1 / 4, 1 / 2] := by
  rw [harmonicExtension, explicit_finePrecision_inv]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [coarseWeight, coarseSeed, observation, Matrix.mul_apply,
      Matrix.conjTranspose_apply, Matrix.one_apply, Fin.sum_univ_succ]

/-- Transposition reverses the ordered response factors and differs from the response here. -/
theorem harmonicExtension_not_symmetric :
    (harmonicExtension fineMatrix coarseWeight observation)ᵀ ≠
      harmonicExtension fineMatrix coarseWeight observation := by
  rw [explicit_harmonicExtension]
  intro h
  have hentry := congrArg (fun M => M 0 1) h
  norm_num [Matrix.transpose_apply] at hentry

theorem explicit_coarse_covariance :
    coarseCovariance fineMatrix coarseWeight observation =
      !![(16 / 15 : ℝ), 2 / 15; 2 / 15, 19 / 15] := by
  rw [coarseCovariance, fineMatrix_inv, coarseWeight_inv]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [observation, Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_succ]

theorem explicit_coarse_precision :
    coarsePrecision fineMatrix coarseWeight observation =
      !![(19 / 20 : ℝ), -1 / 10; -1 / 10, 4 / 5] := by
  rw [← coarseCovariance_inv observation fineMatrix_posDef coarseWeight_posDef,
    explicit_coarse_covariance]
  apply Matrix.inv_eq_right_inv
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.mul_apply, Matrix.one_apply, Fin.sum_univ_succ]

theorem explicit_determinants :
    (finePrecision fineMatrix coarseWeight observation).det = 20 ∧
      (coarsePrecision fineMatrix coarseWeight observation).det = 3 / 4 := by
  rw [explicit_finePrecision, explicit_coarse_precision]
  norm_num [Matrix.det_fin_two]

theorem unique_minimizer (y x : Fin 2 → ℝ) :
    (∀ z, quadraticEnergy fineMatrix coarseWeight observation y x ≤
      quadraticEnergy fineMatrix coarseWeight observation y z) ↔
      x = !![(7 / 20 : ℝ), -3 / 10; 1 / 4, 1 / 2] *ᵥ y := by
  rw [is_minimizer_iff observation fineMatrix_posDef coarseWeight_posDef,
    explicit_harmonicExtension]

end GaussianBlockSpin.MatrixWeighted.Examples
