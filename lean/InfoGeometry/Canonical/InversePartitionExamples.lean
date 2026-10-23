/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.DrazinMoorePenrosePartition
import Mathlib.Data.Matrix.Notation

/-!
# Exact matrix witnesses and countermodels for inverse partitions

These matrices instantiate the ring/star-ring theorems. They do not replace
the operator carriers of those theorems. Every matrix identity is checked
entrywise over the reals, without numerical approximation.
-/

noncomputable section
namespace InfoGeometry.Canonical.InversePartitionExamples

open InfoGeometry.Canonical.Drazin
open InfoGeometry.Singular.MoorePenrose
open InfoGeometry.Singular.MoorePenroseSectors

/-- Standard orthonormal three-node shift. -/
def shift3 : Matrix (Fin 3) (Fin 3) ℝ := !![0, 1, 0; 0, 0, 1; 0, 0, 0]

theorem shift3_cube : shift3 ^ 3 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [shift3, pow_succ, Matrix.mul_apply, Fin.sum_univ_succ]

theorem shift3_drazin : IsDrazinInverse shift3 0 3 := by
  refine ⟨by simp, by simp, ?_⟩
  simp [shift3_cube]

theorem shift3_mp : IsMoorePenroseInverse shift3 shift3.transpose := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [shift3, Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_succ]
  · ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [shift3, Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_succ]
  · change (shift3 * shift3.transpose).conjTranspose = _
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [shift3, Matrix.conjTranspose_apply, Matrix.mul_apply,
        Matrix.transpose_apply, Fin.sum_univ_succ]
  · change (shift3.transpose * shift3).conjTranspose = _
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [shift3, Matrix.conjTranspose_apply, Matrix.mul_apply,
        Matrix.transpose_apply, Fin.sum_univ_succ]

/-- Full matrix equality, including all off-diagonal entries. -/
theorem shift3_boundary_charge :
    shift3 * shift3.transpose - shift3.transpose * shift3 =
      Matrix.diagonal ![1, 0, -1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [shift3, Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_succ]

theorem shift3_boundary_square :
    (shift3 * shift3.transpose - shift3.transpose * shift3) ^ 2 =
      Matrix.diagonal ![1, 0, 1] := by
  rw [shift3_boundary_charge]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [pow_two, Matrix.mul_apply, Fin.sum_univ_succ]

theorem shift3_interior :
    sector (shift3 * shift3.transpose) (shift3.transpose * shift3) (false, false) =
      Matrix.diagonal ![0, 1, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [sector, part, shift3, Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_succ]

/-- A nilpotent directed acyclic operator whose support projectors do NOT commute. -/
def skewChain : Matrix (Fin 4) (Fin 4) ℝ :=
  !![0, 1, 0, 1; 0, 0, 1, 0; 0, 0, 0, 0; 0, 0, 0, 0]

def skewChainMP : Matrix (Fin 4) (Fin 4) ℝ :=
  !![0, 0, 0, 0; 1/2, 0, 0, 0; 0, 1, 0, 0; 1/2, 0, 0, 0]

theorem skewChain_cube : skewChain ^ 3 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [skewChain, pow_succ, Matrix.mul_apply, Fin.sum_univ_succ]

theorem skewChain_mp : IsMoorePenroseInverse skewChain skewChainMP := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [skewChain, skewChainMP, Matrix.mul_apply, Fin.sum_univ_succ]
  · ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [skewChain, skewChainMP, Matrix.mul_apply, Fin.sum_univ_succ]
  · change (skewChain * skewChainMP).conjTranspose = _
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [skewChain, skewChainMP, Matrix.conjTranspose_apply,
        Matrix.mul_apply, Fin.sum_univ_succ]
  · change (skewChainMP * skewChain).conjTranspose = _
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [skewChain, skewChainMP, Matrix.conjTranspose_apply,
        Matrix.mul_apply, Fin.sum_univ_succ]

theorem skewChain_supports_not_commute :
    ¬ Commute (skewChain * skewChainMP) (skewChainMP * skewChain) := by
  intro h
  have he := congrArg (fun M : Matrix (Fin 4) (Fin 4) ℝ => M 1 3) h.eq
  norm_num [skewChain, skewChainMP, Matrix.mul_apply, Fin.sum_univ_succ] at he

theorem skewChain_boundary_square :
    (skewChain * skewChainMP - skewChainMP * skewChain) ^ 2 =
      Matrix.diagonal ![1, 1/2, 1, 1/2] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [skewChain, skewChainMP, pow_two, Matrix.mul_apply, Fin.sum_univ_succ]

/-- Nilpotency alone does not make the squared commutator a projector. -/
theorem skewChain_boundary_not_idempotent :
    ¬ IsIdempotentElem ((skewChain * skewChainMP - skewChainMP * skewChain) ^ 2) := by
  rw [skewChain_boundary_square]
  intro h
  have he := congrArg (fun M : Matrix (Fin 4) (Fin 4) ℝ => M 1 1) h
  norm_num [Matrix.mul_apply, Fin.sum_univ_succ] at he

/-- An idempotent is a Drazin witness without being an orthogonal projection. -/
def oblique : Matrix (Fin 2) (Fin 2) ℝ := !![1, 1; 0, 0]

theorem oblique_drazin : IsDrazinInverse oblique oblique 1 := by
  apply Drazin.IsDrazinInverse.of_idempotent
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [oblique, Matrix.mul_apply, Fin.sum_univ_succ]

theorem oblique_not_selfAdjoint : ¬ IsSelfAdjoint oblique := by
  intro h
  have he := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 1) h
  change oblique.conjTranspose 0 1 = oblique 0 1 at he
  norm_num [oblique, Matrix.conjTranspose_apply] at he

end InfoGeometry.Canonical.InversePartitionExamples
