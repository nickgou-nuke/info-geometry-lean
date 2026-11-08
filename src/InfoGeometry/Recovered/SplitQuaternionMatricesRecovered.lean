/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Split-quaternion 2×2 real matrix core

This recovered module now contains only kernel-checked matrix facts.  Former
Clifford/CAR/amplituhedron claims that depended on unproved bridge lemmas are
not installed here.
-/

namespace InfoGeometry.SplitQuaternion

open Matrix

/-- The identity matrix. -/
def splitOne : Matrix (Fin 2) (Fin 2) ℝ := 1

/-- Generator squaring to `-1`. -/
def splitI : Matrix (Fin 2) (Fin 2) ℝ := ![![0, 1], ![-1, 0]]

/-- Generator squaring to `1`. -/
def splitJ : Matrix (Fin 2) (Fin 2) ℝ := ![![0, 1], ![1, 0]]

/-- Diagonal generator squaring to `1`. -/
def splitK : Matrix (Fin 2) (Fin 2) ℝ := ![![1, 0], ![0, -1]]

/-- Entrywise multiplication for `2 × 2` matrices.  Keeping this expansion
explicit avoids relying on simplifier unfolding of the bundled matrix product. -/
private lemma matrix_mul_fin_two_apply
    (A B : Matrix (Fin 2) (Fin 2) ℝ) (i j : Fin 2) :
    (A * B) i j = A i 0 * B 0 j + A i 1 * B 1 j := by
  rw [Matrix.mul_apply, Fin.sum_univ_two]

@[simp] lemma splitI_sq : splitI * splitI = -splitOne := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    rw [matrix_mul_fin_two_apply] <;>
    simp [splitI, splitOne, Matrix.neg_apply, Matrix.of_apply] <;> ring

@[simp] lemma splitJ_sq : splitJ * splitJ = splitOne := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    rw [matrix_mul_fin_two_apply] <;>
    simp [splitJ, splitOne, Matrix.neg_apply, Matrix.of_apply] <;> ring

@[simp] lemma splitK_sq : splitK * splitK = splitOne := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    rw [matrix_mul_fin_two_apply] <;>
    simp [splitK, splitOne, Matrix.neg_apply, Matrix.of_apply] <;> ring

@[simp] lemma splitI_mul_splitJ : splitI * splitJ = splitK := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    rw [matrix_mul_fin_two_apply] <;>
    simp [splitI, splitJ, splitK, Matrix.neg_apply, Matrix.of_apply] <;> ring

@[simp] lemma splitJ_mul_splitI : splitJ * splitI = -splitK := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    rw [matrix_mul_fin_two_apply, Matrix.neg_apply] <;>
    simp [splitJ, splitI, splitK]

/-- The split-quaternion generators are noncommutative. -/
theorem splitJ_mul_splitI_ne_splitI_mul_splitJ :
    (splitJ * splitI : Matrix (Fin 2) (Fin 2) ℝ) ≠ splitI * splitJ := by
  intro h
  rw [splitJ_mul_splitI, splitI_mul_splitJ] at h
  have h' := congrArg (fun M => M 0 0) h
  change (-1 : ℝ) = 1 at h'
  norm_num at h'

/-- The generator anticommutator is zero. -/
theorem splitJ_splitI_anticommutator_zero :
    splitJ * splitI + splitI * splitJ = 0 := by
  rw [splitJ_mul_splitI, splitI_mul_splitJ]
  exact neg_add_cancel splitK

@[simp] lemma splitJ_mul_splitK : splitJ * splitK = -splitI := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    rw [matrix_mul_fin_two_apply, Matrix.neg_apply] <;>
    simp [splitJ, splitK, splitI]

@[simp] lemma splitK_mul_splitJ : splitK * splitJ = splitI := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    rw [matrix_mul_fin_two_apply] <;>
    simp [splitK, splitJ, splitI, Matrix.neg_apply, Matrix.of_apply] <;> ring

@[simp] lemma splitK_mul_splitI : splitK * splitI = splitJ := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    rw [matrix_mul_fin_two_apply] <;>
    simp [splitK, splitI, splitJ, Matrix.neg_apply, Matrix.of_apply] <;> ring

@[simp] lemma splitI_mul_splitK : splitI * splitK = -splitJ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    rw [matrix_mul_fin_two_apply, Matrix.neg_apply] <;>
    simp [splitI, splitK, splitJ]

/-- Split-quaternion conjugation/adjugate for a 2×2 matrix. -/
def splitConj (M : Matrix (Fin 2) (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  ![![M 1 1, -M 0 1], ![-M 1 0, M 0 0]]

/-- Determinant/norm of a 2×2 matrix. -/
def splitNorm (M : Matrix (Fin 2) (Fin 2) ℝ) : ℝ :=
  M 0 0 * M 1 1 - M 0 1 * M 1 0

lemma mul_splitConj (M : Matrix (Fin 2) (Fin 2) ℝ) :
    M * splitConj M = (splitNorm M) • splitOne := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    rw [matrix_mul_fin_two_apply] <;>
    simp [splitConj, splitNorm, splitOne, Matrix.neg_apply,
      Matrix.of_apply, Matrix.smul_apply, smul_eq_mul] <;>
    ring

lemma splitConj_mul (M : Matrix (Fin 2) (Fin 2) ℝ) :
    splitConj M * M = (splitNorm M) • splitOne := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    rw [matrix_mul_fin_two_apply] <;>
    simp [splitConj, splitNorm, splitOne, Matrix.neg_apply,
      Matrix.of_apply, Matrix.smul_apply, smul_eq_mul] <;>
    ring

lemma split_inverse_theorem (M : Matrix (Fin 2) (Fin 2) ℝ) (h : splitNorm M ≠ 0) :
    M * ((splitNorm M)⁻¹ • splitConj M) = splitOne := by
  rw [Matrix.mul_smul, mul_splitConj, smul_smul, inv_mul_cancel₀ h, one_smul]

/-- Spacetime coordinate embedding in the split-quaternion basis. -/
noncomputable def spacetimeMatrix (t x y z : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![t + z, x + y; -x + y, t - z]

/-- Determinant of the split-quaternion spacetime matrix. -/
lemma det_spacetimeMatrix (t x y z : ℝ) :
    (spacetimeMatrix t x y z).det = t ^ 2 + x ^ 2 - y ^ 2 - z ^ 2 := by
  rw [Matrix.det_fin_two]
  change (t + z) * (t - z) - (x + y) * (-x + y) = _
  ring

end InfoGeometry.SplitQuaternion
