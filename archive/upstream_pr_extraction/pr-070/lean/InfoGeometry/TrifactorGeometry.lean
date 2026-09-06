import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic

/-!
# Trifactor Geometry — Signed Volume, Pfaffian, Berezinian
-/

noncomputable section

namespace TrifactorGeometry

open Matrix

def I₂ : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, 1]
def s1 : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]
def s2 : Matrix (Fin 2) (Fin 2) ℂ := !![0, -Complex.I; Complex.I, 0]
def s3 : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]

def null_mat : Matrix (Fin 2) (Fin 2) ℂ := !![1, 1; 1, 1]
def A_even : Matrix (Fin 2) (Fin 2) ℂ := !![(2:ℂ),0;0,2]
def D_odd  : Matrix (Fin 2) (Fin 2) ℂ := !![(1:ℂ),0;0,-1]
def J_skew : Matrix (Fin 2) (Fin 2) ℂ := !![0,1;-1,0]

def pfaffian2 (A : Matrix (Fin 2) (Fin 2) ℂ) : ℂ := A 0 1

theorem J_skew_sq : J_skew * J_skew = -I₂ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [J_skew, I₂, Matrix.mul_apply, Fin.sum_univ_two]

theorem s1_sq : s1 * s1 = I₂ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [s1, I₂, Matrix.mul_apply, Fin.sum_univ_two]

theorem s2_sq : s2 * s2 = I₂ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [s2, I₂, Matrix.mul_apply, Fin.sum_univ_two, Complex.I_sq]

theorem s3_sq : s3 * s3 = I₂ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [s3, I₂, Matrix.mul_apply, Fin.sum_univ_two]

theorem J_skew_eq_I_s2 : J_skew = Complex.I • s2 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [J_skew, s2, Matrix.smul_apply, Complex.I_sq]

theorem pfaffian2_sq_eq_det_of_skew
    (A : Matrix (Fin 2) (Fin 2) ℂ)
    (hskew : A.transpose = -A) :
    pfaffian2 A ^ 2 = A.det := by
  have h00 : A 0 0 = -A 0 0 := by
    simpa using congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 0 0) hskew
  have h11 : A 1 1 = -A 1 1 := by
    simpa using congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 1 1) hskew
  have h10 : A 1 0 = -A 0 1 := by
    simpa using congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 0 1) hskew
  have hz00 : A 0 0 = 0 := by
    linear_combination h00 / 2
  have hz11 : A 1 1 = 0 := by
    linear_combination h11 / 2
  rw [pfaffian2, Matrix.det_fin_two]
  simp [hz00, hz11, h10]
  ring

theorem det_plus_one_I : I₂.det = (1 : ℂ) := by
  rw [Matrix.det_fin_two]
  norm_num [I₂]

theorem det_plus_one_symplectic : J_skew.det = (1 : ℂ) := by
  rw [Matrix.det_fin_two]
  norm_num [J_skew]
theorem det_minus_one_pauli : s1.det = (-1 : ℂ) ∧ s2.det = (-1 : ℂ) ∧ s3.det = (-1 : ℂ) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [Matrix.det_fin_two]
    norm_num [s1]
  · rw [Matrix.det_fin_two]
    norm_num [s2]
  · rw [Matrix.det_fin_two]
    norm_num [s3]

theorem det_zero_null : null_mat.det = (0 : ℂ) := by
  rw [Matrix.det_fin_two]
  norm_num [null_mat]

theorem berezinian_example : A_even.det / D_odd.det = (-4 : ℂ) := by
  simp [A_even, D_odd, Matrix.det_fin_two] <;> ring

end TrifactorGeometry
