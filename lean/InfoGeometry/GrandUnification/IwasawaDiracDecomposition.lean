import Mathlib.Data.Real.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic

namespace InfoGeometry.GrandUnification.IwasawaDiracDecomposition

open Matrix

local notation "RealMat" => Matrix (Fin 2) (Fin 2) ℝ

-- The three traceless matrices below are a basis of sl(2, ℝ).
-- `matOne` is separately included for the scalar direction in gl(2, ℝ).
def matOne : RealMat := !![1, 0; 0, 1]
def matI_R : RealMat := !![0, -1; 1, 0]
def matJ_R : RealMat := !![1, 0; 0, -1]
def matN_R : RealMat := !![0, 1; 0, 0]

noncomputable def P_plus : RealMat := (1/2 : ℝ) • (matOne + matJ_R)
noncomputable def P_minus : RealMat := (1/2 : ℝ) • (matOne - matJ_R)

lemma mat_mul_expand (A B : RealMat) (i j : Fin 2) :
  (A * B) i j = A i 0 * B 0 j + A i 1 * B 1 j := by
  rw [Matrix.mul_apply, Fin.sum_univ_two]

-- 1. Nilpotency of the N matrix
theorem matN_R_sq : matN_R * matN_R = 0 := by
  ext i j; fin_cases i <;> fin_cases j
  all_goals { rw [mat_mul_expand]; dsimp [matN_R]; ring }

/-- Every displayed traceless matrix has the following coordinates in the
concrete basis `matI_R`, `matJ_R`, `matN_R`. This is a vector-space identity,
not a group-level Iwasawa factorization. -/
theorem iwasawa_decomposition (a b c : ℝ) :
  !![a, b; c, -a] = c • matI_R + a • matJ_R + (b + c) • matN_R := by
  ext i j; fin_cases i <;> fin_cases j
  all_goals { dsimp [matI_R, matJ_R, matN_R, Matrix.add_apply, Matrix.smul_apply]; ring }

/-- The coordinates in `iwasawa_decomposition` are unique. -/
theorem iwasawa_decomposition_unique (a b c a' b' c' : ℝ)
    (h : c • matI_R + a • matJ_R + (b + c) • matN_R =
      c' • matI_R + a' • matJ_R + (b' + c') • matN_R) :
    a = a' ∧ b = b' ∧ c = c' := by
  have h00 := congrArg (fun M : RealMat => M 0 0) h
  have h01 := congrArg (fun M : RealMat => M 0 1) h
  have h10 := congrArg (fun M : RealMat => M 1 0) h
  simp [matI_R, matJ_R, matN_R, Matrix.add_apply] at h00 h01 h10
  constructor
  · linarith
  constructor
  · linarith
  · linarith

-- 3. Spectral expansion over projectors
theorem scale_peirce_spectrum (a : ℝ) :
  a • matJ_R = a • P_plus - a • P_minus := by
  ext i j; fin_cases i <;> fin_cases j
  all_goals { dsimp [matJ_R, P_plus, P_minus, matOne, Matrix.sub_apply, Matrix.smul_apply, Matrix.add_apply]; ring }

-- 4. Nilpotent action over projectors
theorem N_shear_P_minus : matN_R * P_minus = matN_R := by
  ext i j; fin_cases i <;> fin_cases j
  all_goals { rw [mat_mul_expand]; dsimp [matN_R, P_minus, matOne, matJ_R, Matrix.smul_apply, Matrix.sub_apply]; ring }

theorem N_annihilate_P_plus : matN_R * P_plus = 0 := by
  ext i j; fin_cases i <;> fin_cases j
  all_goals { rw [mat_mul_expand]; dsimp [matN_R, P_plus, matOne, matJ_R, Matrix.smul_apply, Matrix.add_apply]; ring }

theorem P_plus_N_P_minus : P_plus * (matN_R * P_minus) = matN_R := by
  rw [N_shear_P_minus]; ext i j; fin_cases i <;> fin_cases j
  all_goals { rw [mat_mul_expand]; dsimp [matN_R, P_plus, matOne, matJ_R, Matrix.smul_apply, Matrix.add_apply]; ring }

-- 5. The Log-Determinant Trace Functional
lemma matrix_trace_fin_two (A : RealMat) : Matrix.trace A = A 0 0 + A 1 1 := by
  dsimp [Matrix.trace, Matrix.diag]
  rw [Fin.sum_univ_two]

theorem trace_matI_R : Matrix.trace matI_R = 0 := by
  rw [matrix_trace_fin_two]
  dsimp [matI_R]; ring

theorem trace_matJ_R : Matrix.trace matJ_R = 0 := by
  rw [matrix_trace_fin_two]
  dsimp [matJ_R]; ring

theorem trace_matN_R : Matrix.trace matN_R = 0 := by
  rw [matrix_trace_fin_two]
  dsimp [matN_R]; ring

theorem trace_matOne : Matrix.trace matOne = 2 := by
  rw [matrix_trace_fin_two]
  dsimp [matOne]; ring

theorem trace_iwasawa (a b c : ℝ) :
  Matrix.trace (c • matI_R + a • matJ_R + (b + c) • matN_R) = 0 := by
  rw [matrix_trace_fin_two]
  dsimp [matI_R, matJ_R, matN_R, Matrix.add_apply, Matrix.smul_apply]
  ring

end InfoGeometry.GrandUnification.IwasawaDiracDecomposition
