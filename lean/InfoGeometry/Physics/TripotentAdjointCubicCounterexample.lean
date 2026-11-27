/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib
import InfoGeometry.Physics.TripotentAdjointDerivation

/-!
# A tripotent matrix need not have a tripotent inner commutator action

The cubic identity for `ad_P` follows from the stronger hypothesis `P^2 = P`.
The owner `GrassmannianBundleCyclotomicOrientability.adjoint_idempotent_cubic`
already proves that generic result for every associative ring. This file records
the boundary: the weaker element equation `P^3 = P` does not suffice, even for
a concrete noncommutative matrix algebra.
-/

namespace InfoGeometry.Physics.TripotentAdjointCubicCounterexample

open InfoGeometry.Physics.Algebra
open scoped Matrix

abbrev Operator := Matrix (Fin 2) (Fin 2) ℝ

/-- A non-diagonal tripotent operator with `p^2 = 1`. -/
def p : Operator := !![1, 1; 0, -1]

/-- A matrix unit that does not commute with `p`. -/
def e₁₂ : Operator := !![0, 1; 0, 0]

theorem p_sq : p * p = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [p, Matrix.mul_apply, Fin.sum_univ_two]

theorem p_trip : p * p * p = p := by
  calc
    p * p * p = (p * p) * p := by simp [mul_assoc]
    _ = p := by rw [p_sq, one_mul]

theorem p_not_idempotent : p * p ≠ p := by
  rw [p_sq]
  intro h
  have h₀₁ := congrArg (fun M : Operator => M 0 1) h
  norm_num [p] at h₀₁

theorem ad_p_e₁₂ : adOp p e₁₂ = 2 • e₁₂ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [adOp, p, e₁₂, Matrix.mul_apply, Fin.sum_univ_two]

theorem ad_p_cube_e₁₂ :
    adOp p (adOp p (adOp p e₁₂)) = 8 • e₁₂ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [adOp, p, e₁₂, Matrix.mul_apply, Fin.sum_univ_two]

/-- The hypothesis `p^3 = p` alone does not imply `ad_p^3 = ad_p`.
The witnessing operators are noncommuting 2-by-2 matrices; `p` itself is
non-diagonal. -/
theorem tripotent_does_not_imply_adjoint_cubic :
    p * p * p = p ∧
      adOp p (adOp p (adOp p e₁₂)) ≠ adOp p e₁₂ := by
  constructor
  · exact p_trip
  · rw [ad_p_cube_e₁₂, ad_p_e₁₂]
    intro h
    have h₀₁ := congrArg (fun M : Operator => M 0 1) h
    norm_num [e₁₂] at h₀₁

/-- Explicit non-commutativity witness on `Matrix (Fin 2) (Fin 2) ℝ`. -/
theorem tripotent_mat2r_noncomm_exists :
    ∃ A B : Matrix (Fin 2) (Fin 2) ℝ, A * B ≠ B * A := by
  refine ⟨p, e₁₂, fun h => ?_⟩
  have h2 := ad_p_e₁₂
  rw [adOp, h, sub_self] at h2
  have h01 := congrArg (fun M : Operator => M 0 1) h2.symm
  norm_num [e₁₂] at h01

end InfoGeometry.Physics.TripotentAdjointCubicCounterexample
