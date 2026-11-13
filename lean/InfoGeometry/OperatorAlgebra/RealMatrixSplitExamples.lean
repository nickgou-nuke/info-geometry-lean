/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib.Algebra.Star.Module
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Tactic

/-!
# Exact real two-dimensional examples for the matrix adjoint split

The user-supplied example has positive metric and nondegenerate alternating
part, but its raised-index operator squares to `-(1/4) • 1`, not `-1`.
-/

noncomputable section

namespace InfoGeometry.OperatorAlgebra.RealMatrixSplitExamples

open Matrix

/-- The real matrix in the intake. -/
def sampleMatrix : Matrix (Fin 2) (Fin 2) ℝ := !![2, 3; 1, 4]

/-- Its symmetric part. -/
def sampleMetric : Matrix (Fin 2) (Fin 2) ℝ := !![2, 2; 2, 4]

/-- Its skew-symmetric part. -/
def sampleSkew : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; -1, 0]

/-- The resulting raised-index operator, with all entries real. -/
def sampleRaised : Matrix (Fin 2) (Fin 2) ℝ := !![1 / 2, 1; -1 / 2, -1 / 2]

theorem sample_selfAdjointPart :
    (selfAdjointPart ℝ sampleMatrix : Matrix (Fin 2) (Fin 2) ℝ) = sampleMetric := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [selfAdjointPart_apply_coe, sampleMatrix, sampleMetric, Matrix.star_apply]

theorem sample_skewAdjointPart :
    (skewAdjointPart ℝ sampleMatrix : Matrix (Fin 2) (Fin 2) ℝ) = sampleSkew := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [skewAdjointPart_apply_coe, sampleMatrix, sampleSkew, Matrix.star_apply]

theorem sampleMetric_isSymm : sampleMetric.IsSymm := by
  change sampleMetricᵀ = sampleMetric
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [sampleMetric, Matrix.transpose_apply]

theorem sampleSkew_transpose : sampleSkewᵀ = -sampleSkew := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [sampleSkew, Matrix.transpose_apply]

/-- Positivity is proved for all nonzero real vectors, rather than inferred from symmetry. -/
theorem sampleMetric_posDef : sampleMetric.PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos
  · exact Matrix.isHermitian_iff_isSymm.mpr sampleMetric_isSymm
  · intro x hx
    simp [sampleMetric, dotProduct, mulVec, Fin.sum_univ_two]
    by_cases h1 : x 1 = 0
    · have h0 : x 0 ≠ 0 := by
        intro h0
        apply hx
        ext i
        fin_cases i <;> simp_all
      nlinarith [sq_pos_of_ne_zero h0]
    · nlinarith [sq_nonneg (x 0 + x 1), sq_pos_of_ne_zero h1]

theorem sampleMetric_det : sampleMetric.det = 4 := by
  norm_num [sampleMetric, Matrix.det_fin_two]

theorem sampleSkew_det : sampleSkew.det = 1 := by
  norm_num [sampleSkew, Matrix.det_fin_two]

/-- The alternating form in the example is nondegenerate. -/
theorem sampleSkew_toBilin'_nondegenerate : sampleSkew.toBilin'.Nondegenerate := by
  apply LinearMap.BilinForm.nondegenerate_toBilin'_iff_det_ne_zero.mpr
  rw [sampleSkew_det]
  norm_num

/-- Both ordered products are retained in the commutator computation. -/
theorem sample_commutator :
    sampleMetric * sampleSkew - sampleSkew * sampleMetric = !![-4, -2; -2, 4] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [sampleMetric, sampleSkew, Matrix.mul_apply, Fin.sum_univ_two]

theorem sample_parts_do_not_commute : sampleMetric * sampleSkew ≠ sampleSkew * sampleMetric := by
  intro h
  have hc := sample_commutator
  rw [h, sub_self] at hc
  have h00 := congrArg (fun N : Matrix (Fin 2) (Fin 2) ℝ => N 0 0) hc
  norm_num at h00

theorem sampleMetric_inv : sampleMetric⁻¹ = !![1, -1 / 2; -1 / 2, 1 / 2] := by
  apply Matrix.inv_eq_right_inv
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [sampleMetric, Matrix.mul_apply, Fin.sum_univ_two]

theorem sampleRaised_eq : sampleMetric⁻¹ * sampleSkew = sampleRaised := by
  rw [sampleMetric_inv]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [sampleSkew, sampleRaised, Matrix.mul_apply, Fin.sum_univ_two]

theorem sampleRaised_sq :
    sampleRaised * sampleRaised = (-1 / 4 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [sampleRaised, Matrix.mul_apply, Fin.sum_univ_two]

/-- Even a positive metric and nondegenerate skew form do not force `A² = -1`. -/
theorem sampleRaised_not_complex :
    sampleRaised * sampleRaised ≠ -(1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  intro h
  rw [sampleRaised_sq] at h
  have h00 := congrArg (fun N : Matrix (Fin 2) (Fin 2) ℝ => N 0 0) h
  norm_num at h00

/-- Invertibility of the original matrix does not prevent its skew part from vanishing. -/
theorem invertible_with_zero_skew_part :
    ∃ M : Matrix (Fin 2) (Fin 2) ℝ,
      IsUnit M ∧ (skewAdjointPart ℝ M : Matrix (Fin 2) (Fin 2) ℝ) = 0 := by
  refine ⟨1, isUnit_one, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [skewAdjointPart_apply_coe, Matrix.star_apply]

/-- An invertible skew matrix has vanishing symmetric part in positive dimension. -/
theorem invertible_with_zero_symmetric_part :
    ∃ M : Matrix (Fin 2) (Fin 2) ℝ,
      IsUnit M ∧ (selfAdjointPart ℝ M : Matrix (Fin 2) (Fin 2) ℝ) = 0 := by
  refine ⟨sampleSkew, ?_, ?_⟩
  · apply (Matrix.isUnit_iff_isUnit_det _).mpr
    rw [sampleSkew_det]
    exact isUnit_one
  · ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [selfAdjointPart_apply_coe, sampleSkew, Matrix.star_apply]

end InfoGeometry.OperatorAlgebra.RealMatrixSplitExamples
