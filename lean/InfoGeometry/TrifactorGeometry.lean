import Mathlib.Data.Matrix.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

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

theorem det_plus_one_I : I₂.det = (1 : ℂ) := by simp [I₂, Matrix.det_fin_two]
theorem det_plus_one_symplectic : J_skew.det = (1 : ℂ) := by simp [J_skew, Matrix.det_fin_two]
theorem det_minus_one_pauli : s1.det = (-1 : ℂ) ∧ s2.det = (-1 : ℂ) ∧ s3.det = (-1 : ℂ) := by
  refine ⟨?_, ?_, ?_⟩
  · simp [s1, Matrix.det_fin_two]
  · simp [s2, Matrix.det_fin_two]
  · simp [s3, Matrix.det_fin_two]
theorem det_zero_null : null_mat.det = (0 : ℂ) := by simp [null_mat, Matrix.det_fin_two]
theorem pfaffian_sq_eq_det : (J_skew 0 1) ^ 2 = J_skew.det := by simp [J_skew, Matrix.det_fin_two]
theorem berezinian_example : A_even.det / D_odd.det = (-4 : ℂ) := by
  simp [A_even, D_odd, Matrix.det_fin_two] <;> ring

end TrifactorGeometry
