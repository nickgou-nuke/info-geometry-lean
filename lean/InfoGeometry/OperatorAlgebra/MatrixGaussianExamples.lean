/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.MatrixGaussianComposition
import InfoGeometry.OperatorAlgebra.GaussianNoiseComposition
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# A noncommuting rectangular Gaussian channel

A three-dimensional input passes through two two-dimensional noisy
observations. The positive noise precisions do not commute, and the second
observation is not a scaled coisometry. Exact rational entries fix both the
transport order and the resulting Gaussian law.
-/

noncomputable section

namespace InfoGeometry.OperatorAlgebra.MatrixGaussianExamples

open Matrix ProbabilityTheory
open scoped ProbabilityTheory ComplexOrder
open PositiveCoarseGraining MatrixGaussianKernel

def firstSeed : Matrix (Fin 2) (Fin 2) ℝ := !![1, 1; 0, 0]
def secondSeed : Matrix (Fin 2) (Fin 2) ℝ := !![1, 0; 1, 0]
def firstPrecision : Matrix (Fin 2) (Fin 2) ℝ := 1 + firstSeedᴴ * firstSeed
def secondPrecision : Matrix (Fin 2) (Fin 2) ℝ := 1 + secondSeedᴴ * secondSeed
def firstObservation : Matrix (Fin 2) (Fin 3) ℝ := !![1, 0, 1; 0, 1, 1]
def secondObservation : Matrix (Fin 2) (Fin 2) ℝ := !![1, 2; 0, 1]

theorem firstPrecision_posDef : firstPrecision.PosDef :=
  Matrix.PosDef.one.add_posSemidef (Matrix.posSemidef_conjTranspose_mul_self firstSeed)

theorem secondPrecision_posDef : secondPrecision.PosDef :=
  Matrix.PosDef.one.add_posSemidef (Matrix.posSemidef_conjTranspose_mul_self secondSeed)

theorem firstPrecision_eq : firstPrecision = !![(2 : ℝ), 1; 1, 2] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [firstPrecision, firstSeed, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Matrix.one_apply, Fin.sum_univ_succ]

theorem secondPrecision_eq : secondPrecision = !![(3 : ℝ), 0; 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [secondPrecision, secondSeed, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Matrix.one_apply, Fin.sum_univ_succ]

theorem noisePrecisions_do_not_commute :
    firstPrecision * secondPrecision ≠ secondPrecision * firstPrecision := by
  intro h
  have he := congrArg (fun M => M 0 1) h
  norm_num [firstPrecision_eq, secondPrecision_eq, Matrix.mul_apply,
    Fin.sum_univ_succ] at he

theorem secondObservation_not_scaled_coisometry :
    ¬ ∃ s : ℝ, secondObservation * secondObservationᴴ =
      s • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  rintro ⟨s, h⟩
  have he := congrArg (fun M => M 0 1) h
  norm_num [secondObservation, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Matrix.one_apply, Fin.sum_univ_succ] at he

theorem firstPrecision_inv :
    firstPrecision⁻¹ = !![(2 / 3 : ℝ), -1 / 3; -1 / 3, 2 / 3] := by
  apply Matrix.inv_eq_right_inv
  rw [firstPrecision_eq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.mul_apply, Matrix.one_apply, Fin.sum_univ_succ]

theorem secondPrecision_inv :
    secondPrecision⁻¹ = !![(1 / 3 : ℝ), 0; 0, 1] := by
  apply Matrix.inv_eq_right_inv
  rw [secondPrecision_eq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.mul_apply, Matrix.one_apply, Fin.sum_univ_succ]

theorem collapsedCovariance_eq :
    coarseCovariance firstPrecision secondPrecision secondObservation =
      !![(7 / 3 : ℝ), 1; 1, 5 / 3] := by
  rw [coarseCovariance, firstPrecision_inv, secondPrecision_inv]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [secondObservation, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Matrix.vecMul, dotProduct, Matrix.transpose_apply, Fin.sum_univ_succ]

theorem collapsedPrecision_eq :
    coarsePrecision firstPrecision secondPrecision secondObservation =
      !![(15 / 26 : ℝ), -9 / 26; -9 / 26, 21 / 26] := by
  rw [← coarseCovariance_inv secondObservation firstPrecision_posDef
    secondPrecision_posDef, collapsedCovariance_eq]
  apply Matrix.inv_eq_right_inv
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.mul_apply, Matrix.one_apply, Fin.sum_univ_succ]

theorem compositeObservation_eq :
    secondObservation * firstObservation = !![(1 : ℝ), 2, 3; 0, 1, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [firstObservation, secondObservation, Matrix.mul_apply, Fin.sum_univ_succ]

/-- The concrete result is equality of probability kernels, with the exact
noncommuting noise calculation substituted into the general theorem. -/
theorem noncommuting_gaussianKernel_comp :
    gaussianKernel secondObservation secondPrecision ∘ₖ
        gaussianKernel firstObservation firstPrecision =
      gaussianKernel !![(1 : ℝ), 2, 3; 0, 1, 1]
        !![(15 / 26 : ℝ), -9 / 26; -9 / 26, 21 / 26] := by
  rw [gaussianKernel_comp firstObservation secondObservation firstPrecision_posDef
    secondPrecision_posDef, compositeObservation_eq, collapsedPrecision_eq]

end InfoGeometry.OperatorAlgebra.MatrixGaussianExamples
