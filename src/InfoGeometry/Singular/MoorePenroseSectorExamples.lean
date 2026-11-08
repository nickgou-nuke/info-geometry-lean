/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Singular.MoorePenroseSectors
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# Finite witnesses for the support-sector hypotheses

All matrices use the standard orthonormal coordinate basis and column action.
The four-dimensional example is nilpotent but its support boundary square is
not idempotent. Thus nilpotence cannot replace support commutation.
-/

namespace InfoGeometry.Singular.MoorePenroseSectorExamples
open Matrix MoorePenrose

def chain3 : Matrix (Fin 3) (Fin 3) ℝ := !![0, 1, 0; 0, 0, 1; 0, 0, 0]

theorem chain3_penrose : IsMoorePenroseInverse chain3 chain3.transpose := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [chain3, Matrix.mul_apply, Matrix.vecMul, dotProduct,
      Matrix.transpose_apply, Fin.sum_univ_succ, Matrix.star_eq_conjTranspose]

/-- Full matrix equalities, including the off-diagonal entries. -/
theorem chain3_supports :
    chain3 * chain3.transpose = diagonal ![1, 1, 0] ∧
    chain3.transpose * chain3 = diagonal ![0, 1, 1] := by
  constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [chain3, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.diagonal]

def skewChain : Matrix (Fin 4) (Fin 4) ℝ :=
  !![0, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 0; 0, 0, 1, 0]

/-- Even the orthonormal shift and its pseudoinverse do not commute. -/
theorem chain3_inverse_noncommuting :
    ¬ Commute chain3 chain3.transpose := by
  change chain3 * chain3.transpose ≠ chain3.transpose * chain3
  rw [chain3_supports.1, chain3_supports.2]
  intro h
  have h00 := congrArg (fun T : Matrix (Fin 3) (Fin 3) ℝ => T 0 0) h
  norm_num [Matrix.diagonal] at h00

theorem chain3_matrix_noncommutativity :
    chain3 * chain3.transpose ≠ chain3.transpose * chain3 := by
  exact chain3_inverse_noncommuting

def chain3T : Matrix (Fin 3) (Fin 3) ℝ := chain3.transpose

theorem chain3_named_matrix_noncommutativity :
    chain3 * chain3T ≠ chain3T * chain3 := by
  simpa [chain3T] using chain3_matrix_noncommutativity

noncomputable def skewChainMP : Matrix (Fin 4) (Fin 4) ℝ :=
  !![0, 0, 0, 0; 1, 0, 0, 0; 0, 1/2, 0, 1/2; 0, 0, 0, 0]

theorem skewChain_inverse_noncommuting : skewChain * skewChainMP ≠ skewChainMP * skewChain := by
  intro h
  have h00 := congrArg (fun T : Matrix (Fin 4) (Fin 4) ℝ => T 0 0) h
  norm_num [skewChain, skewChainMP, Matrix.mul_apply, Fin.sum_univ_succ] at h00

theorem skewChain_nilpotent : skewChain ^ 3 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [skewChain, pow_succ, Matrix.mul_apply, Fin.sum_univ_succ]

theorem skewChain_penrose : IsMoorePenroseInverse skewChain skewChainMP := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [skewChain, skewChainMP, Matrix.mul_apply, Fin.sum_univ_succ,
      Matrix.star_eq_conjTranspose]

theorem skewChain_boundary_square :
    (skewChain * skewChainMP - skewChainMP * skewChain)^2 =
      diagonal ![1, (1/2 : ℝ), 1, 1/2] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [skewChain, skewChainMP, pow_two, Matrix.mul_apply,
      Fin.sum_univ_succ, Matrix.diagonal]

/-- A nilpotent MP pair whose proposed boundary square is not a projector. -/
theorem skewChain_boundary_not_idempotent :
    let B := (skewChain * skewChainMP - skewChainMP * skewChain)^2
    B * B ≠ B := by
  dsimp
  rw [skewChain_boundary_square]
  intro h
  have h11 := congrArg (fun T : Matrix (Fin 4) (Fin 4) ℝ => T 1 1) h
  norm_num [Matrix.mul_apply, Fin.sum_univ_succ, Matrix.diagonal] at h11

end InfoGeometry.Singular.MoorePenroseSectorExamples
