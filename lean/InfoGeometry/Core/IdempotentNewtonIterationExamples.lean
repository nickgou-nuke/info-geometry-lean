/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Core.IdempotentDefectIteration
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# A noncommutative matrix requiring two Newton corrections

In the full ring of three-by-three integer matrices, the operator `1 + J`,
where `J` is a length-three nilpotent Jordan chain, has a defect of nilpotence
index three. One correction does not suffice, while two corrections give the
identity. The operator does not commute with the displayed first-coordinate
idempotent. This is an exact finite example of the arbitrary-ring theorem;
no diagonal or commuting model is imposed on that theorem.
-/

namespace InfoGeometry.Core.IdempotentNewtonIterationExamples

open InfoGeometry.Core.IdempotentGraphGrassmannian

abbrev Op := Matrix (Fin 3) (Fin 3) ℤ

/-- An identity plus a length-three nilpotent chain. -/
def chain : Op := !![1, 1, 0; 0, 1, 1; 0, 0, 1]

/-- The first-coordinate cut used to witness noncommutativity. -/
def cut : Op := !![1, 0, 0; 0, 0, 0; 0, 0, 0]

theorem cut_idempotent : cut * cut = cut := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [cut, Matrix.mul_apply, Fin.sum_univ_succ]

theorem chain_cut_noncommute : chain * cut ≠ cut * chain := by
  intro h
  have h01 := congrArg (fun x : Op => x 0 1) h
  norm_num [chain, cut, Matrix.mul_apply, Fin.sum_univ_succ] at h01

theorem chain_defect :
    idempotencyDefect chain = !![0, 1, 1; 0, 0, 1; 0, 0, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [idempotencyDefect, chain, Matrix.mul_apply, Fin.sum_univ_succ]

theorem chain_defect_sq :
    idempotencyDefect chain ^ 2 = !![0, 0, 1; 0, 0, 0; 0, 0, 0] := by
  rw [chain_defect]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [pow_two, Matrix.mul_apply, Fin.sum_univ_succ]

theorem chain_defect_sq_ne_zero : idempotencyDefect chain ^ 2 ≠ 0 := by
  rw [chain_defect_sq]
  intro h
  have h02 := congrArg (fun x : Op => x 0 2) h
  norm_num at h02

theorem chain_defect_cube_zero : idempotencyDefect chain ^ 3 = 0 := by
  rw [pow_succ, chain_defect_sq, chain_defect]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.mul_apply, Fin.sum_univ_succ]

theorem chain_first_correction :
    newtonPeirceStep chain = !![1, 0, -3; 0, 1, 0; 0, 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [newtonPeirceStep, chain, Matrix.mul_apply,
      Matrix.ofNat_apply, Fin.sum_univ_succ]

theorem chain_first_correction_not_idempotent :
    newtonPeirceStep chain * newtonPeirceStep chain ≠ newtonPeirceStep chain := by
  rw [chain_first_correction]
  intro h
  have h02 := congrArg (fun x : Op => x 0 2) h
  norm_num [Matrix.mul_apply, Fin.sum_univ_succ] at h02

theorem chain_second_correction : newtonPeirceStep^[2] chain = 1 := by
  change newtonPeirceStep (newtonPeirceStep chain) = 1
  rw [chain_first_correction]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [newtonPeirceStep, Matrix.mul_apply,
      Matrix.ofNat_apply, Fin.sum_univ_succ]

/-- The generic termination theorem applies with `m = 3` and `n = 2`. -/
theorem chain_second_correction_idempotent :
    newtonPeirceStep^[2] chain * newtonPeirceStep^[2] chain =
      newtonPeirceStep^[2] chain := by
  exact newtonPeirceStep_iterates_idempotent_of_defect_pow_eq_zero
    chain_defect_cube_zero (by norm_num)

/-- The stationary tail is obtained from the arbitrary-ring stability theorem. -/
theorem chain_later_corrections (k : ℕ) : newtonPeirceStep^[2 + k] chain = 1 := by
  rw [newtonPeirceStep_iterates_stable_of_defect_pow_eq_zero
    chain_defect_cube_zero (show 3 ≤ 2 ^ 2 by norm_num), chain_second_correction]

end InfoGeometry.Core.IdempotentNewtonIterationExamples
