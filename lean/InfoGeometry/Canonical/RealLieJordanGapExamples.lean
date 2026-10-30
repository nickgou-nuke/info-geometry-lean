/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.RealLieJordanScaling
import InfoGeometry.Canonical.RealLieJordanExamples
import InfoGeometry.Core.LieJordanModeActions

/-!
# Dense noncommuting witnesses for mode actions and scaling

The existing dense real corner and its transpose remain full matrices.
Exact entries refute selective stationarity, the proposed coefficient four,
and skew-plus stationarity of the Gram sum. Separate nonzero image witnesses
establish nonvacuity for the vector and matrix operator gap complements.
-/

noncomputable section

namespace InfoGeometry.Canonical.RealLieJordanGapExamples

open Matrix RealLieJordanExamples RealLieJordanGap RealLieJordanScaling
open RealLieJordanGeometry Core.LieJordanGenerators Core.LieJordanModeActions
open Core.PeirceGrading
open scoped Matrix InnerProductSpace

attribute [local instance 100] LieRing.ofAssociativeRing

theorem U_square_zero : U * U = 0 := by
  have h := (corners_sq_zero P_idempotent S).1
  change U ^ 2 = 0 at h
  simpa only [pow_two] using h

theorem U_transpose_square_zero : U.transpose * U.transpose = 0 := by
  rw [← Matrix.transpose_mul, U_square_zero, Matrix.transpose_zero]

/-- The sum mode is not stationary for the symmetric generator. -/
theorem symmetric_sum_entry :
    (symmetricGenerator (R := ℝ) U U.transpose (U + U.transpose)) 0 0 = 5096 / 81 := by
  rw [symmetricGenerator_sum U_square_zero U_transpose_square_zero]
  change -(2 * ∑ k : Fin 3,
    (U * U.transpose + U.transpose * U) 0 k * (U + U.transpose) k 0) = _
  simp only [gram_apply]
  norm_num [Matrix.add_apply, Matrix.transpose_apply, U_apply,
    probe, Fin.sum_univ_succ]

theorem symmetric_sum_ne_zero :
    symmetricGenerator (R := ℝ) U U.transpose (U + U.transpose) ≠ 0 := by
  intro h
  have he := congrArg (fun x : Mat3 => x 0 0) h
  rw [symmetric_sum_entry] at he
  norm_num at he

theorem symmetric_difference_entry :
    (symmetricGenerator (R := ℝ) U U.transpose (U - U.transpose)) 0 1 = -980 / 27 := by
  rw [symmetricGenerator_difference U_square_zero U_transpose_square_zero]
  change -(2 * ∑ k : Fin 3,
    (U * U.transpose + U.transpose * U) 0 k * (U - U.transpose) k 1) = _
  simp only [gram_apply]
  norm_num [Matrix.sub_apply, Matrix.transpose_apply, U_apply,
    probe, Fin.sum_univ_succ]

/-- The proposed factor four is false on the same dense noncommuting carrier. -/
theorem symmetric_difference_ne_neg_four :
    symmetricGenerator (R := ℝ) U U.transpose (U - U.transpose) ≠
      -((4 : ℝ) • ((U * U.transpose + U.transpose * U) * (U - U.transpose))) := by
  intro h
  have he := congrArg (fun x : Mat3 => x 0 1) h
  rw [symmetric_difference_entry] at he
  change (-980 / 27 : ℝ) = -(4 * ∑ k : Fin 3,
    (U * U.transpose + U.transpose * U) 0 k * (U - U.transpose) k 1) at he
  simp only [gram_apply] at he
  norm_num [Matrix.sub_apply, Matrix.transpose_apply, U_apply,
    probe, Fin.sum_univ_succ] at he

theorem skewPlus_gram_entry :
    (skewPlusGenerator (R := ℝ) U U.transpose
      (U * U.transpose + U.transpose * U)) 0 0 = -27832 / 243 := by
  rw [skewPlusGenerator_quadratic P_idempotent
    U_mem_peirce10 U_transpose_mem_peirce01]
  simp only [Matrix.smul_apply, nsmul_eq_mul, Nat.cast_ofNat]
  change 4 * ∑ k : Fin 3,
    (⁅U, U.transpose⁆ : Mat3) 0 k * (U * U.transpose + U.transpose * U) k 0 = _
  simp only [bracket_apply, gram_apply]
  norm_num [probe, Fin.sum_univ_succ]

theorem skewPlus_gram_ne_zero :
    skewPlusGenerator (R := ℝ) U U.transpose
      (U * U.transpose + U.transpose * U) ≠ 0 := by
  intro h
  have he := congrArg (fun x : Mat3 => x 0 0) h
  rw [skewPlus_gram_entry] at he
  norm_num at he

/-- Every nonzero seed rescaling retains the exhibited noncommutation. -/
theorem rescaled_U_noncommuting {r : ℝ} (hr : r ≠ 0) :
    (r • U) * (r • U).transpose ≠ (r • U).transpose * (r • U) :=
  smul_mul_transpose_ne_transpose_mul U_mul_transpose_ne_transpose_mul hr

/-- The actual Gram operator has a nonzero active vector on its Euclidean carrier. -/
theorem gram_has_nonzero_active_vector :
    ∃ x : EuclideanSpace ℝ (Fin 3),
      x ∈ (U * U.transpose + U.transpose * U).toEuclideanLin.kerᗮ ∧ x ≠ 0 := by
  let T : Module.End ℝ (EuclideanSpace ℝ (Fin 3)) :=
    (U * U.transpose + U.transpose * U).toEuclideanLin
  let e : EuclideanSpace ℝ (Fin 3) := WithLp.toLp 2 (Pi.single (0 : Fin 3) (1 : ℝ))
  have hT : T.IsPositive := gram_toEuclideanLin_isPositive U
  have hentry : (T e) 0 = (89 / 9 : ℝ) := by
    change ((U * U.transpose + U.transpose * U) *ᵥ
      Pi.single (0 : Fin 3) (1 : ℝ)) 0 = (89 / 9 : ℝ)
    rw [Matrix.mulVec_single_one]
    change (U * U.transpose + U.transpose * U) 0 0 = (89 / 9 : ℝ)
    rw [gram_apply]
    norm_num [probe]
  refine ⟨T e, ?_, ?_⟩
  · change T e ∈ T.kerᗮ
    rw [LinearMap.orthogonal_ker T, hT.adjoint_eq]
    exact ⟨e, rfl⟩
  · intro hz
    have he := congrArg (fun x : EuclideanSpace ℝ (Fin 3) => x 0) hz
    rw [hentry] at he
    norm_num at he

theorem gram_no_uniform_positive_bound :
    ¬ ∃ c : ℝ, 0 < c ∧ ∀ r : ℝ, 0 < r →
      ∀ x ∈ ((r • U) * (r • U).transpose +
          (r • U).transpose * (r • U)).toEuclideanLin.kerᗮ,
        c * ‖x‖ ^ 2 ≤ inner ℝ x
          (((r • U) * (r • U).transpose +
            (r • U).transpose * (r • U)).toEuclideanLin x) :=
  gram_not_exists_uniform_positive_bound U gram_has_nonzero_active_vector

section MatrixOperator

open scoped InfoGeometry.Canonical.RealLieJordanGeometry

theorem generator_projection_entry :
    (symmetricGenerator (R := ℝ) U U.transpose P) 0 0 = 142 / 27 := by
  rw [symmetricGenerator_projection P_idempotent
    U_mem_peirce10 U_transpose_mem_peirce01]
  simp only [Matrix.neg_apply, Matrix.smul_apply]
  norm_num [bracket_apply, probe]

/-- An actual generator image witnesses the entire centralizer complement. -/
theorem generator_has_nonzero_active_matrix :
    ∃ x : Mat3, x ∈ (Subalgebra.centralizer ℝ
        ({U, U.transpose} : Set Mat3)).toSubmoduleᗮ ∧ x ≠ 0 := by
  refine ⟨symmetricGenerator (R := ℝ) U U.transpose P, ?_, ?_⟩
  · rw [← range_symmetricGenerator_eq_centralizer_orthogonal]
    exact ⟨P, rfl⟩
  · intro h
    have he := congrArg (fun x : Mat3 => x 0 0) h
    rw [generator_projection_entry] at he
    norm_num at he

theorem generator_no_uniform_positive_bound :
    ¬ ∃ c : ℝ, 0 < c ∧ ∀ r : ℝ, 0 < r →
      ∀ x ∈ (Subalgebra.centralizer ℝ
          ({r • U, (r • U).transpose} : Set Mat3)).toSubmoduleᗮ,
        c * ‖x‖ ^ 2 ≤ inner ℝ x
          ((-symmetricGenerator (R := ℝ) (r • U) (r • U).transpose) x) :=
  generator_not_exists_uniform_positive_bound U generator_has_nonzero_active_matrix

end MatrixOperator

end InfoGeometry.Canonical.RealLieJordanGapExamples
