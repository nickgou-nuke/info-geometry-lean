/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Algebra.FiniteMatrixNoncommutativity
import InfoGeometry.OperatorAlgebra.PeirceHodgeCoercivity
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# Noncommuting finite witness with a nontrivial harmonic sector

The theorems quantify over every input in the full 3-by-3 real matrix algebra.
This witness checks the interfaces; it is not an interacting infinite model.
-/

namespace InfoGeometry.OperatorAlgebra.PeirceHodgeExamples

open Matrix HilbertSchmidtMatrix
open scoped Matrix
open InfoGeometry.OperatorAlgebra.PeirceHodgeCoercivity

/-- A non-diagonal square-zero boundary coefficient. -/
def jump : Matrix (Fin 3) (Fin 3) ℝ := !![1, -1, 1; 1, -1, 1; 0, 0, 0]

/-- Retain the actual matrix quadratic coefficient. -/
def quadratic : Matrix (Fin 3) (Fin 3) ℝ := jump * jumpᵀ + jumpᵀ * jump

/-- Non-diagonal projection onto the one-dimensional coefficient kernel. -/
noncomputable def harmonic : Matrix (Fin 3) (Fin 3) ℝ :=
  !![(1/6 : ℝ), -1/6, -1/3; -1/6, 1/6, 1/3; -1/3, 1/3, 2/3]

theorem jump_sq_zero : jump * jump = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [jump, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_succ]

theorem jump_noncommutes : jump * jumpᵀ ≠ jumpᵀ * jump := by
  intro h
  have he := congrArg (fun a : Matrix (Fin 3) (Fin 3) ℝ => a 0 1) h
  norm_num [jump, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_succ] at he

theorem harmonic_sq : harmonic * harmonic = harmonic := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [harmonic, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_succ]

theorem harmonic_transpose : harmonicᵀ = harmonic := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [harmonic]

theorem harmonic_ne_zero : harmonic ≠ 0 := by
  intro h
  have he := congrArg (fun a : Matrix (Fin 3) (Fin 3) ℝ => a 2 2) h
  norm_num [harmonic] at he

theorem quadratic_eq : quadratic = (6 : ℝ) • (1 - harmonic) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [quadratic, jump, harmonic, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_succ]

theorem quadratic_annihilates_harmonic : quadratic * harmonic = 0 := by
  rw [quadratic_eq, smul_mul_assoc, sub_mul, one_mul, harmonic_sq, sub_self, smul_zero]

/-- The lower bound is proved for all matrix inputs, not only eigenvectors. -/
theorem coercivity (x : Matrix (Fin 3) (Fin 3) ℝ) :
    6 * hilbertSchmidtPairing (x - harmonic * x * harmonic)
      (x - harmonic * x * harmonic) ≤
        hilbertSchmidtPairing x (quadratic * x + x * quadratic) := by
  apply full_matrix_corner_coercivity harmonic_sq harmonic_transpose quadratic (by norm_num)
  rw [quadratic_eq, sub_self]
  exact Matrix.PosSemidef.zero

end InfoGeometry.OperatorAlgebra.PeirceHodgeExamples
