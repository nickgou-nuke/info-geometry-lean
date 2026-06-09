import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Notation

/-!
# Trifactor Projectors — Lean 4

Concrete projectors P₊, P₋, P₀ on 2×2 matrices.
M = P₊ - P₋ always; P₊+P₋+P₀ = I always.
Tested on σ₃, projector, identity.
-/

noncomputable section

namespace TrifactorProjectors

open Matrix

def I2 : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, 1]
def s3 : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]
def null_mat : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, 0]

/-- P₊ = (M²+M)/2 -/
def P_plus (M : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ := (M*M + M) / (2 : ℂ)
/-- P₋ = (M²-M)/2 -/
def P_minus (M : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ := (M*M - M) / (2 : ℂ)
/-- P₀ = I - M² -/
def P_zero (M : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ := I2 - M*M

/-- P₊ + P₋ + P₀ = I — always true. -/
theorem projector_sum (M : Matrix (Fin 2) (Fin 2) ℂ) :
    P_plus M + P_minus M + P_zero M = I2 := by
  unfold P_plus P_minus P_zero
  ext i j; fin_cases i <;> fin_cases j <;> simp [I2, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

/-- M = P₊ - P₋ — always true. -/
theorem op_eq_plus_minus_minus (M : Matrix (Fin 2) (Fin 2) ℂ) :
    P_plus M - P_minus M = M := by
  unfold P_plus P_minus
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring

/-- σ₃ satisfies σ₃³ = σ₃ (since σ₃² = I). -/
theorem s3_cube_eq_s3 : s3*s3*s3 = s3 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [s3, Matrix.mul_apply, Fin.sum_univ_two]

/-- The projector P has P² = P, hence P³ = P. -/
theorem proj_cube_eq_proj : null_mat*null_mat*null_mat = null_mat := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [null_mat, Matrix.mul_apply, Fin.sum_univ_two]

/-- I satisfies I³ = I. -/
theorem I_cube_eq_I : I2*I2*I2 = I2 := by
  simp [I2]

/-- For σ₃: P₊ = diag(1,0), P₋ = diag(0,1), P₀ = 0. -/
theorem s3_decomposition : P_plus s3 = !![(1:ℂ),0; 0,0] ∧ P_minus s3 = !![0,0; 0,(1:ℂ)] ∧ P_zero s3 = 0 := by
  unfold P_plus P_minus P_zero
  refine ⟨?_, ?_, ?_⟩
  · ext i j; fin_cases i <;> fin_cases j <;> simp [s3, I2, Matrix.mul_apply, Fin.sum_univ_two]
  · ext i j; fin_cases i <;> fin_cases j <;> simp [s3, I2, Matrix.mul_apply, Fin.sum_univ_two]
  · ext i j; fin_cases i <;> fin_cases j <;> simp [s3, I2, Matrix.mul_apply, Fin.sum_univ_two]

end TrifactorProjectors
