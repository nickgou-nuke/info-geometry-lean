/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Routing.FunctionalRouteCore
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-! Exact causal-route witnesses separating token depths, operator shells,
ambient transpose, and support commutation. No inverse predicate is replaced. -/
namespace InfoGeometry.Routing.FunctionalRouteObstructions
open Matrix
open InfoGeometry.Canonical.Drazin
open InfoGeometry.Canonical.Drazin.IsDrazinInverse
open InfoGeometry.Singular.MoorePenrose
noncomputable section

/-- Two siblings at depth two, after a depth-one relay. -/
def branchA : Matrix (Fin 4) (Fin 4) ℝ :=
  !![1,0,0,0; 1,0,0,0; 0,1,0,0; 0,1,0,0]
def branchD : Matrix (Fin 4) (Fin 4) ℝ :=
  !![1,0,0,0; 1,0,0,0; 1,0,0,0; 1,0,0,0]
def branchN : Matrix (Fin 4) (Fin 4) ℝ :=
  !![0,0,0,0; 0,0,0,0; -1,1,0,0; -1,1,0,0]
def branchMP : Matrix (Fin 4) (Fin 4) ℝ :=
  !![0,0,-1/4,-1/4; 0,0,1/4,1/4; 0,0,0,0; 0,0,0,0]

theorem branch_drazin : IsDrazinInverse branchA branchD 2 := by
  refine ⟨?_, ?_, ?_⟩ <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [branchA, branchD, pow_succ, Matrix.mul_apply, Fin.sum_univ_succ,
      Matrix.one_apply]

theorem branch_nilpotent : nilpotent branchA branchD = branchN := by
  rw [nilpotent_eq_mul_complementaryProjection]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [branchA, branchD, branchN, complementaryProjection, projection,
      Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply]

theorem branch_mp : IsMoorePenroseInverse branchN branchMP := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [branchN, branchMP, Matrix.mul_apply, Fin.sum_univ_succ]
  · ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [branchN, branchMP, Matrix.mul_apply, Fin.sum_univ_succ]
  · change (branchN * branchMP).conjTranspose = _
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [branchN, branchMP, Matrix.mul_apply, Matrix.conjTranspose_apply,
        Fin.sum_univ_succ]
  · change (branchMP * branchN).conjTranspose = _
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [branchN, branchMP, Matrix.mul_apply, Matrix.conjTranspose_apply,
        Fin.sum_univ_succ]

/-- The zeroth dressed shell is not the diagonal depth-one selector. -/
theorem branch_shell_zero :
    (1 - branchA * branchD) * (1 - branchN * branchMP) * (1 - branchA * branchD) =
      !![0,0,0,0; -1,1,0,0; 0,0,1/2,-1/2; 0,0,-1/2,1/2] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [branchA, branchD, branchN, branchMP, Matrix.mul_apply,
      Fin.sum_univ_succ, Matrix.one_apply]

/-- Two depth-two tokens can cancel after only one routing step. -/
theorem sibling_contrast_dies :
    Matrix.vecMul ![0,0,1,-1] branchA = (0 : Fin 4 → ℝ) := by
  funext j
  fin_cases j <;>
    norm_num [branchA, Matrix.vecMul, dotProduct, Fin.sum_univ_succ]

/-- A causal chain already invalidates automatic MP-support compatibility. -/
def chainN : Matrix (Fin 4) (Fin 4) ℝ :=
  !![0,0,0,0; 0,0,0,0; -1,1,0,0; -1,0,1,0]
def chainMP : Matrix (Fin 4) (Fin 4) ℝ :=
  !![0,0,-1/3,-1/3; 0,0,2/3,-1/3; 0,0,-1/3,2/3; 0,0,0,0]
def chainA : Matrix (Fin 4) (Fin 4) ℝ :=
  !![1,0,0,0; 1,0,0,0; 0,1,0,0; 0,0,1,0]

theorem chain_drazin : IsDrazinInverse chainA branchD 3 := by
  refine ⟨?_, ?_, ?_⟩ <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [chainA, branchD, pow_succ, Matrix.mul_apply, Fin.sum_univ_succ,
      Matrix.one_apply]

theorem chain_nilpotent : nilpotent chainA branchD = chainN := by
  rw [nilpotent_eq_mul_complementaryProjection]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [chainA, branchD, chainN, complementaryProjection, projection,
      Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply]

theorem chain_mp : IsMoorePenroseInverse chainN chainMP := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [chainN, chainMP, Matrix.mul_apply, Fin.sum_univ_succ]
  · ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [chainN, chainMP, Matrix.mul_apply, Fin.sum_univ_succ]
  · change (chainN * chainMP).conjTranspose = _
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [chainN, chainMP, Matrix.mul_apply, Matrix.conjTranspose_apply,
        Fin.sum_univ_succ]
  · change (chainMP * chainN).conjTranspose = _
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [chainN, chainMP, Matrix.mul_apply, Matrix.conjTranspose_apply,
        Fin.sum_univ_succ]

theorem chain_supports_do_not_commute :
    ¬ Commute (chainN * chainMP) (chainMP * chainN) := by
  intro h
  have he := congrArg (fun M : Matrix (Fin 4) (Fin 4) ℝ => M 0 2) h.eq
  norm_num [chainN, chainMP, Matrix.mul_apply, Fin.sum_univ_succ] at he

theorem chain_squared_charge :
    (chainN * chainMP - chainMP * chainN) ^ 2 =
      !![2/3,-1/3,0,0; -1/3,2/3,0,0; 0,0,1/3,0; 0,0,0,1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [chainN, chainMP, pow_two, Matrix.mul_apply, Fin.sum_univ_succ]

theorem chain_squared_charge_not_idempotent :
    ¬ IsIdempotentElem ((chainN * chainMP - chainMP * chainN) ^ 2) := by
  rw [chain_squared_charge]
  intro h
  have he := congrArg (fun M : Matrix (Fin 4) (Fin 4) ℝ => M 2 2) h
  norm_num [Matrix.mul_apply, Fin.sum_univ_succ] at he

/-- A nonpermutation route can have N=0 while its nilpotent projector is nonzero. -/
def constantA : Matrix (Fin 2) (Fin 2) ℝ := !![1,0;1,0]

theorem constant_drazin : IsDrazinInverse constantA constantA 1 := by
  apply IsDrazinInverse.of_idempotent
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [constantA, Matrix.mul_apply, Fin.sum_univ_succ]

theorem constant_nilpotent_zero : nilpotent constantA constantA = 0 := by
  rw [nilpotent_eq_mul_complementaryProjection]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [constantA, complementaryProjection, projection, Matrix.mul_apply,
      Fin.sum_univ_succ, Matrix.one_apply]

theorem constant_inverse_not_core_transpose :
    constantA ≠ (core constantA constantA).transpose := by
  intro h
  have he := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 1) h
  norm_num [core, constantA, Matrix.transpose_apply, Matrix.mul_apply,
    Fin.sum_univ_succ] at he

end
end InfoGeometry.Routing.FunctionalRouteObstructions
