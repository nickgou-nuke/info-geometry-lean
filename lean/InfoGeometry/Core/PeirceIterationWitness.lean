/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Core.PeirceQuadraticIteration
import Mathlib

/-! # Dense real matrix regression for all-order inner action -/
namespace InfoGeometry.Core.PeirceIterationWitness
attribute [local instance 100] LieRing.ofAssociativeRing
open Matrix PeirceDecomposition PeirceQuadraticIteration
noncomputable section

abbrev Mat := Matrix (Fin 4) (Fin 4) ℝ

def p : Mat := !![1/2, 1/2, 0, 0; 1/2, 1/2, 0, 0;
  0, 0, 1/2, 1/2; 0, 0, 1/2, 1/2]
def u : Mat := !![1, -1, 2, -2; 1, -1, 2, -2;
  3, -3, 4, -4; 3, -3, 4, -4]
def v : Mat := u.transpose

theorem p_idempotent : IsIdempotentElem p := by
  change p * p = p
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [p, Matrix.mul_apply, Fin.sum_univ_succ]

theorem p_mul_u : p * u = u := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [p, u, Matrix.mul_apply, Fin.sum_univ_succ]

theorem u_mul_p : u * p = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [p, u, Matrix.mul_apply, Fin.sum_univ_succ]

theorem p_mul_v : p * v = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [p, u, v, Matrix.mul_apply, Fin.sum_univ_succ]

theorem v_mul_p : v * p = v := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [p, u, v, Matrix.mul_apply, Fin.sum_univ_succ]

theorem u_mem : u ∈ peirce10 p := by
  refine ⟨u, ?_⟩
  simp [complementIdempotent, mul_sub, p_mul_u, u_mul_p]

theorem v_mem : v ∈ peirce01 p := by
  refine ⟨v, ?_⟩
  simp [complementIdempotent, sub_mul, p_mul_v, v_mul_p]

theorem arrows_not_commuting : u * v ≠ v * u := by
  intro h
  have h00 := congrArg (fun a : Mat => a 0 0) h
  norm_num [u, v, Matrix.mul_apply, Fin.sum_univ_succ] at h00

/-- An off-diagonal entry forbids replacing the operator weight by a scalar. -/
theorem weight_not_scalar : ¬ ∃ r : ℝ, 2 * (u * v + v * u) = r • (1 : Mat) := by
  rintro ⟨r, h⟩
  have h02 := congrArg (fun a : Mat => a 0 2) h
  norm_num [two_mul, u, v, Matrix.mul_apply, Fin.sum_univ_succ] at h02

/-- A nonzero first action rules out a vacuous constant frame. -/
theorem first_action_ne_zero : LieAlgebra.ad ℝ Mat ⁅u, v⁆ (u + v) ≠ 0 := by
  rw [weighted_sum_step ℝ p_idempotent u_mem v_mem]
  intro h
  have h01 := congrArg (fun a : Mat => a 0 1) h
  norm_num [two_mul, u, v, Matrix.mul_apply, Fin.sum_univ_succ] at h01

/-- All orders specialize on the same dense, genuinely noncommuting carrier. -/
theorem all_orders (n : ℕ) :
    (LieAlgebra.ad ℝ Mat ⁅u, v⁆ ^ (2 * n)) (u + v) =
      (2 * (u * v + v * u)) ^ (2 * n) * (u + v) ∧
    (LieAlgebra.ad ℝ Mat ⁅u, v⁆ ^ (2 * n + 1)) (u + v) =
      (2 * (u * v + v * u)) ^ (2 * n + 1) * (u - v) :=
  ⟨ad_pow_sum_even ℝ p_idempotent u_mem v_mem n,
   ad_pow_sum_odd ℝ p_idempotent u_mem v_mem n⟩

end
end InfoGeometry.Core.PeirceIterationWitness
