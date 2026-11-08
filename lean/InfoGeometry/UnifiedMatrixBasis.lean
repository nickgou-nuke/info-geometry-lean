import Mathlib.Data.Matrix.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.Matrix.Notation

/-!
# Unified Matrix Basis — Lean 4

Pauli matrices, complex structures, quaternion relations, Hilbert-Schmidt.
-/

noncomputable section

namespace UnifiedMatrixBasis

open Matrix

def I₂ : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, 1]
def σ₁ : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]
def σ₂ : Matrix (Fin 2) (Fin 2) ℂ := !![0, -Complex.I; Complex.I, 0]
def σ₃ : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]

theorem pauli_square : σ₁*σ₁=I₂ ∧ σ₂*σ₂=I₂ ∧ σ₃*σ₃=I₂ := by
  refine ⟨?_, ?_, ?_⟩
  · ext i j; fin_cases i <;> fin_cases j <;> simp [σ₁, I₂, Matrix.mul_apply, Fin.sum_univ_two]
  · ext i j; fin_cases i <;> fin_cases j <;> simp [σ₂, I₂, Matrix.mul_apply, Fin.sum_univ_two]
  · ext i j; fin_cases i <;> fin_cases j <;> simp [σ₃, I₂, Matrix.mul_apply, Fin.sum_univ_two]

theorem pauli_anticomm : σ₁*σ₂+σ₂*σ₁ = (0 : Matrix (Fin 2) (Fin 2) ℂ) ∧
    σ₂*σ₃+σ₃*σ₂ = (0 : Matrix (Fin 2) (Fin 2) ℂ) ∧ σ₃*σ₁+σ₁*σ₃ = (0 : Matrix (Fin 2) (Fin 2) ℂ) := by
  refine ⟨?_, ?_, ?_⟩
  · ext i j; fin_cases i <;> fin_cases j <;> simp [σ₁, σ₂, Matrix.mul_apply, Fin.sum_univ_two]
  · ext i j; fin_cases i <;> fin_cases j <;> simp [σ₂, σ₃, Matrix.mul_apply, Fin.sum_univ_two]
  · ext i j; fin_cases i <;> fin_cases j <;> simp [σ₃, σ₁, Matrix.mul_apply, Fin.sum_univ_two]

def complexI : Matrix (Fin 4) (Fin 4) ℝ := !![0,-1,0,0; 1,0,0,0; 0,0,0,-1; 0,0,1,0]
def complexJ : Matrix (Fin 4) (Fin 4) ℝ := !![0,0,-1,0; 0,0,0,1; 1,0,0,0; 0,-1,0,0]
def complexK : Matrix (Fin 4) (Fin 4) ℝ := !![0,0,0,-1; 0,0,-1,0; 0,1,0,0; 1,0,0,0]

theorem quaternion_relations :
    complexI*complexI = -(1 : Matrix (Fin 4) (Fin 4) ℝ) ∧
    complexJ*complexJ = -(1 : Matrix (Fin 4) (Fin 4) ℝ) ∧
    complexK*complexK = -(1 : Matrix (Fin 4) (Fin 4) ℝ) ∧
    complexI*complexJ = complexK ∧
    complexJ*complexK = complexI ∧
    complexK*complexI = complexJ := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · ext i j; fin_cases i <;> fin_cases j <;> simp [complexI, Matrix.mul_apply, Fin.sum_univ_four]
  · ext i j; fin_cases i <;> fin_cases j <;> simp [complexJ, Matrix.mul_apply, Fin.sum_univ_four]
  · ext i j; fin_cases i <;> fin_cases j <;> simp [complexK, Matrix.mul_apply, Fin.sum_univ_four]
  · ext i j; fin_cases i <;> fin_cases j <;>
      simp [complexI, complexJ, complexK, Matrix.mul_apply, Fin.sum_univ_four]
  · ext i j; fin_cases i <;> fin_cases j <;>
      simp [complexI, complexJ, complexK, Matrix.mul_apply, Fin.sum_univ_four]
  · ext i j; fin_cases i <;> fin_cases j <;>
      simp [complexI, complexJ, complexK, Matrix.mul_apply, Fin.sum_univ_four]

/--
The determinant of the Pauli/Hermitian representative recovers the Minkowski
quadratic form in the coordinates `(dt, dx, dy, dz)`.
-/
theorem metric_equivalence (dt dx dy dz : ℂ) :
    let dX : Matrix (Fin 2) (Fin 2) ℂ := dt • I₂ + dx • σ₁ + dy • σ₂ + dz • σ₃
    Matrix.det dX = dt * dt - (dx * dx + dy * dy + dz * dz) := by
  intro dX
  rw [Matrix.det_fin_two]
  have h00 : dX 0 0 = dt + dz := by
    simp [dX, I₂, σ₁, σ₂, σ₃]
  have h01 : dX 0 1 = dx - dy * Complex.I := by
    simp [dX, I₂, σ₁, σ₂, σ₃]
    ring
  have h10 : dX 1 0 = dx + dy * Complex.I := by
    simp [dX, I₂, σ₁, σ₂, σ₃]
  have h11 : dX 1 1 = dt - dz := by
    simp [dX, I₂, σ₁, σ₂, σ₃]
    ring
  rw [h00, h01, h10, h11]
  ring_nf
  simp [Complex.I_sq]
  ring_nf

def hilbertSchmidt (A B : Matrix (Fin 2) (Fin 2) ℂ) : ℂ := ((∑ i : Fin 2, (A * B) i i) / 2)

theorem hilbertSchmidt_orthonormal : hilbertSchmidt I₂ I₂ = (1 : ℂ) ∧
    hilbertSchmidt σ₁ σ₁ = (1 : ℂ) ∧ hilbertSchmidt σ₂ σ₂ = (1 : ℂ) ∧
    hilbertSchmidt σ₃ σ₃ = (1 : ℂ) ∧ hilbertSchmidt I₂ σ₁ = 0 := by
  unfold hilbertSchmidt
  simp [I₂, σ₁, σ₂, σ₃, Matrix.mul_apply, Fin.sum_univ_two]

end UnifiedMatrixBasis
