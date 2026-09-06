import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Notation

/-!
# Section 2: Vector, Matrix, Quaternion — Lean 4

Pauli matrices, spacetime matrix, complex structures, metric equivalence.
-/

noncomputable section

namespace Section2

open Matrix

def I₂ : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, 1]
def σ₁ : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]
def σ₂ : Matrix (Fin 2) (Fin 2) ℂ := !![0, -Complex.I; Complex.I, 0]
def σ₃ : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]

theorem pauli_square : σ₁ * σ₁ = I₂ ∧ σ₂ * σ₂ = I₂ ∧ σ₃ * σ₃ = I₂ := by
  refine ⟨?_, ?_, ?_⟩
  · ext i j; fin_cases i <;> fin_cases j <;> simp [σ₁, I₂, Matrix.mul_apply, Fin.sum_univ_two]
  · ext i j; fin_cases i <;> fin_cases j <;> simp [σ₂, I₂, Matrix.mul_apply, Fin.sum_univ_two]
  · ext i j; fin_cases i <;> fin_cases j <;> simp [σ₃, I₂, Matrix.mul_apply, Fin.sum_univ_two]

theorem pauli_anticomm : σ₁ * σ₂ + σ₂ * σ₁ = (0 : Matrix (Fin 2) (Fin 2) ℂ) ∧
    σ₂ * σ₃ + σ₃ * σ₂ = (0 : Matrix (Fin 2) (Fin 2) ℂ) ∧
    σ₃ * σ₁ + σ₁ * σ₃ = (0 : Matrix (Fin 2) (Fin 2) ℂ) := by
  refine ⟨?_, ?_, ?_⟩
  · ext i j; fin_cases i <;> fin_cases j <;> simp [σ₁, σ₂]
  · ext i j; fin_cases i <;> fin_cases j <;> simp [σ₂, σ₃]
  · ext i j; fin_cases i <;> fin_cases j <;> simp [σ₃, σ₁]

def complexI : Matrix (Fin 4) (Fin 4) ℝ := !![0,-1,0,0; 1,0,0,0; 0,0,0,-1; 0,0,1,0]
def complexJ : Matrix (Fin 4) (Fin 4) ℝ := !![0,0,-1,0; 0,0,0,1; 1,0,0,0; 0,-1,0,0]
def complexK : Matrix (Fin 4) (Fin 4) ℝ := !![0,0,0,-1; 0,0,-1,0; 0,1,0,0; 1,0,0,0]

theorem I_sq_neg : complexI * complexI = -(1 : Matrix (Fin 4) (Fin 4) ℝ) := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [complexI, Matrix.mul_apply, Fin.sum_univ_four]

theorem J_sq_neg : complexJ * complexJ = -(1 : Matrix (Fin 4) (Fin 4) ℝ) := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [complexJ, Matrix.mul_apply, Fin.sum_univ_four]

theorem K_sq_neg : complexK * complexK = -(1 : Matrix (Fin 4) (Fin 4) ℝ) := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [complexK, Matrix.mul_apply, Fin.sum_univ_four]

theorem IJ_eq_K : complexI * complexJ = complexK := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [complexI, complexJ, complexK, Matrix.mul_apply, Fin.sum_univ_four]

end Section2
