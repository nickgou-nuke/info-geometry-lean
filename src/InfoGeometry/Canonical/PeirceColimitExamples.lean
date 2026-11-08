/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.PeirceDissipatorColimit
import InfoGeometry.Clifford.Cl11ColimitDimension
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Algebra.Order.Star.Real

/-!
# Dense real witnesses inside the actual tensor colimit

A dense projection and symmetric seed in the full four-by-four real matrix
algebra have a dense forward corner. That corner fails to commute with its
transpose. Reindexing identifies this algebra with stage two, and the existing
faithful star-algebra inclusion preserves the nonzero commutator in the limit.
-/

noncomputable section

namespace InfoGeometry.Canonical.PeirceColimitExamples

open Matrix InfoGeometry.Core.PeirceDecomposition InfoGeometry.Core.PeirceGrading
open InfoGeometry.Core.PeirceCoupledCorners
open InfoGeometry.Clifford.Cl11TensorTowerLimit InfoGeometry.Clifford.Cl11StarUniversal
open InfoGeometry.Clifford.TowerMatrix PeirceDissipatorColimit
open scoped Matrix

def P : Matrix (Fin 4) (Fin 4) ℝ :=
  !![8 / 9, -2 / 9, -2 / 15, -8 / 45;
    -2 / 9, 5 / 9, -4 / 15, -16 / 45;
    -2 / 15, -4 / 15, 1 / 5, 4 / 15;
    -8 / 45, -16 / 45, 4 / 15, 16 / 45]
def S : Matrix (Fin 4) (Fin 4) ℝ :=
  !![1, 2, 3, 4; 2, 5, 6, 7; 3, 6, 8, 9; 4, 7, 9, 10]
def U : Matrix (Fin 4) (Fin 4) ℝ := component10 P S

theorem P_idempotent : IsIdempotentElem P := by
  change P * P = P
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [P, Matrix.mul_apply, Fin.sum_univ_succ]

theorem P_transpose : Pᵀ = P := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [P, Matrix.transpose_apply]

theorem P_selfAdjoint : IsSelfAdjoint P := by
  simpa only [IsSelfAdjoint, Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_eq_transpose_of_trivial] using P_transpose

theorem S_transpose : Sᵀ = S := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [S, Matrix.transpose_apply]

theorem P_dense (i j : Fin 4) : P i j ≠ 0 := by
  fin_cases i <;> fin_cases j <;> norm_num [P]

theorem S_dense (i j : Fin 4) : S i j ≠ 0 := by
  fin_cases i <;> fin_cases j <;> norm_num [S]

theorem P_not_commute_S : ¬ Commute P S := by
  intro h
  have he := congrArg (fun x : Matrix (Fin 4) (Fin 4) ℝ => x 0 1) h.eq
  norm_num [P, S, Matrix.mul_apply, Fin.sum_univ_succ] at he

theorem U_apply (i j : Fin 4) : U i j =
    (!![-494 / 675, -988 / 675, -284 / 225, -596 / 675;
      -958 / 675, -1916 / 675, -448 / 225, -1387 / 675;
      241 / 225, 482 / 225, 118 / 75, 337 / 225;
      964 / 675, 1928 / 675, 472 / 225, 1348 / 675] : Matrix (Fin 4) (Fin 4) ℝ) i j := by
  fin_cases i <;> fin_cases j <;>
    simp only [U, component10, complementIdempotent, Matrix.mul_apply, Matrix.sub_apply] <;>
    norm_num [P, S, Fin.sum_univ_succ, Matrix.one_apply]

theorem U_dense (i j : Fin 4) : U i j ≠ 0 := by
  rw [U_apply]
  fin_cases i <;> fin_cases j <;> norm_num

theorem U_mem_peirce10 : U ∈ peirce10 P := component10_mem P S

theorem U_star_mem_peirce01 : star U ∈ peirce01 P :=
  star_mem_peirce01 P_selfAdjoint U_mem_peirce10

theorem U_sq_zero : U * U = 0 := by
  calc
    U * U = U * (P * U) := by rw [left_support10 P_idempotent U_mem_peirce10]
    _ = (U * P) * U := (mul_assoc U P U).symm
    _ = 0 := by rw [right_support10 P_idempotent U_mem_peirce10, zero_mul]

theorem U_mul_star_ne_star_mul : U * star U ≠ star U * U := by
  intro h
  have he := congrArg (fun x : Matrix (Fin 4) (Fin 4) ℝ => x 0 0) h
  simp only [Matrix.mul_apply, Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.transpose_apply] at he
  norm_num [U_apply, Fin.sum_univ_succ] at he

/-- This is ordinary positive-semidefiniteness in the full real matrix algebra. -/
theorem gram_posSemidef : (U * Uᵀ + Uᵀ * U).PosSemidef := by
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
    (Matrix.posSemidef_self_mul_conjTranspose U).add
      (Matrix.posSemidef_conjTranspose_mul_self U)

/-- The quadratic coefficient is not central in the ambient full matrix algebra. -/
theorem gram_not_commute_seed : ¬ Commute (U * Uᵀ + Uᵀ * U) S := by
  intro h
  have he := congrArg (fun x : Matrix (Fin 4) (Fin 4) ℝ => x 0 1) h.eq
  simp only [Matrix.mul_apply, Matrix.add_apply, Matrix.transpose_apply] at he
  norm_num [U_apply, S, Fin.sum_univ_succ] at he

/-- Even on the active corner, the quadratic operator cannot be replaced by
a scalar coefficient. Two exact entries rule out every real scalar. -/
theorem gram_mul_U_ne_smul (r : ℝ) :
    (U * Uᵀ + Uᵀ * U) * U ≠ r • U := by
  intro h
  have h0 := congrArg (fun x : Matrix (Fin 4) (Fin 4) ℝ => x 0 0) h
  have h2 := congrArg (fun x : Matrix (Fin 4) (Fin 4) ℝ => x 0 2) h
  simp only [Matrix.mul_apply, Matrix.add_apply, Matrix.transpose_apply,
    Matrix.smul_apply, smul_eq_mul] at h0 h2
  norm_num [U_apply, Fin.sum_univ_succ] at h0 h2
  linarith

/-- The full four-by-four operator is represented in the actual stage-two algebra. -/
def stageU : Stage 2 := (matEquivFinPowTwo 2).symm U

theorem stageU_sq_zero : stageU * stageU = 0 := by
  change (matEquivFinPowTwo 2).symm U * (matEquivFinPowTwo 2).symm U = 0
  rw [← map_mul, U_sq_zero, map_zero]

theorem stageU_star : star stageU = (matEquivFinPowTwo 2).symm (star U) := by
  ext i j
  rfl

theorem stageU_not_commute_star : ¬ Commute stageU (star stageU) := by
  intro h
  apply U_mul_star_ne_star_mul
  have hh := h.map (matEquivFinPowTwo 2).toRingHom
  change Commute ((matEquivFinPowTwo 2) stageU)
    ((matEquivFinPowTwo 2) (star stageU)) at hh
  rw [stageU_star, stageU, AlgEquiv.apply_symm_apply, AlgEquiv.apply_symm_apply] at hh
  exact hh

/-- Reindexing into the tensor stage preserves the nonscalar action certificate. -/
theorem stage_gram_mul_U_ne_smul (r : ℝ) :
    (stageU * star stageU + star stageU * stageU) * stageU ≠ r • stageU := by
  intro h
  apply gram_mul_U_ne_smul r
  have he := congrArg (matEquivFinPowTwo 2) h
  simp only [stageU_star] at he
  simp only [map_mul, map_add, map_smul, stageU,
    AlgEquiv.apply_symm_apply, Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_eq_transpose_of_trivial] at he
  exact he

/-- The dense finite-stage witness remains square-zero inside the real quotient. -/
theorem limit_U_sq_zero : ofStage 2 stageU * ofStage 2 stageU = 0 :=
  limit_square_zero stageU_sq_zero

/-- The quotient is demonstrably noncommutative, witnessed by an operator and its star. -/
theorem limit_U_not_commute_star :
    ¬ Commute (ofStage 2 stageU) (star (ofStage 2 stageU)) := by
  rw [← ofStage_star, ofStage_commute_iff]
  exact stageU_not_commute_star

/-- Faithful real star-algebra inclusion preserves the nonscalar action
even on the active corner of the infinite-dimensional quotient. -/
theorem limit_gram_mul_U_ne_smul (r : ℝ) :
    let a := ofStage 2 stageU
    (a * star a + star a * a) * a ≠ r • a := by
  dsimp only
  intro h
  apply stage_gram_mul_U_ne_smul r
  apply ofStageStarAlgHom_injective 2
  simpa only [map_mul, map_add, map_smul, map_star, ofStageStarAlgHom_apply] using h

/-- An explicit pair witnesses noncommutation on the existing real limit carrier. -/
theorem limit_noncommutative : ∃ a b : Limit, a * b ≠ b * a :=
  ⟨ofStage 2 stageU, star (ofStage 2 stageU), limit_U_not_commute_star⟩

end InfoGeometry.Canonical.PeirceColimitExamples
