import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Notation

/-!
# Section 5: Clifford Structure — Lean 4 (Pauli-Dirac representation)

γ⁰ = [[I, 0], [0, -I]]  (block diagonal)
γ^i = [[0, σ_i], [-σ_i, 0]]

Clifford: {γ^a, γ^b} = 2·η^{ab}·I₄  with (+---) signature.
-/

noncomputable section

namespace Section5

open Matrix

/-- Pauli matrices as 2×2 blocks. -/
def I₂ : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, 1]
def s1 : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]
def s2 : Matrix (Fin 2) (Fin 2) ℂ := !![0, -Complex.I; Complex.I, 0]
def s3 : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]

/--
Gamma matrices in the Pauli-Dirac representation.
γ⁰ = diag(I, -I), γ^i = [[0, σ_i], [-σ_i, 0]].
-/
def γ0 : Matrix (Fin 4) (Fin 4) ℂ :=
  !![1,0,0,0; 0,1,0,0; 0,0,-1,0; 0,0,0,-1]

def γ1 : Matrix (Fin 4) (Fin 4) ℂ :=
  !![0,0,0,1; 0,0,1,0; 0,-1,0,0; -1,0,0,0]

def γ2 : Matrix (Fin 4) (Fin 4) ℂ :=
  !![0,0,0,-Complex.I; 0,0,Complex.I,0; 0,Complex.I,0,0; -Complex.I,0,0,0]

def γ3 : Matrix (Fin 4) (Fin 4) ℂ :=
  !![0,0,1,0; 0,0,0,-1; -1,0,0,0; 0,1,0,0]

/-- γ⁵ = i·γ⁰·γ¹·γ²·γ³ in the Pauli-Dirac basis. -/
def γ5 : Matrix (Fin 4) (Fin 4) ℂ :=
  Complex.I • (γ0 * γ1 * γ2 * γ3)

/-- Minkowski metric (+---): η^{00}=+1, η^{11}=η^{22}=η^{33}=-1. -/
def η4 : Matrix (Fin 4) (Fin 4) ℂ :=
  !![1,0,0,0; 0,-1,0,0; 0,0,-1,0; 0,0,0,-1]

/-- γ⁰ squares to I. -/
theorem γ0_sq_I : γ0 * γ0 = (1 : Matrix (Fin 4) (Fin 4) ℂ) := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [γ0, Matrix.mul_apply, Fin.sum_univ_four]

/-- γ^i squares to -I for i=1,2,3. -/
theorem γi_sq_neg_I : γ1 * γ1 = -(1 : Matrix (Fin 4) (Fin 4) ℂ) ∧
    γ2 * γ2 = -(1 : Matrix (Fin 4) (Fin 4) ℂ) ∧
    γ3 * γ3 = -(1 : Matrix (Fin 4) (Fin 4) ℂ) := by
  refine ⟨?_, ?_, ?_⟩
  · ext i j; fin_cases i <;> fin_cases j <;> simp [γ1, Matrix.mul_apply, Fin.sum_univ_four]
  · ext i j; fin_cases i <;> fin_cases j <;> simp [γ2, Matrix.mul_apply, Fin.sum_univ_four]
  · ext i j; fin_cases i <;> fin_cases j <;> simp [γ3, Matrix.mul_apply, Fin.sum_univ_four]

/-- Clifford anticommutation {γ^a, γ^b} = 2·η^{ab}·I₄ for the 10 independent cases. -/
theorem clifford_relations :
    γ0 * γ1 + γ1 * γ0 = (0 : Matrix (Fin 4) (Fin 4) ℂ) ∧
    γ0 * γ2 + γ2 * γ0 = (0 : Matrix (Fin 4) (Fin 4) ℂ) ∧
    γ0 * γ3 + γ3 * γ0 = (0 : Matrix (Fin 4) (Fin 4) ℂ) ∧
    γ1 * γ2 + γ2 * γ1 = (0 : Matrix (Fin 4) (Fin 4) ℂ) ∧
    γ1 * γ3 + γ3 * γ1 = (0 : Matrix (Fin 4) (Fin 4) ℂ) ∧
    γ2 * γ3 + γ3 * γ2 = (0 : Matrix (Fin 4) (Fin 4) ℂ) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · ext i j; fin_cases i <;> fin_cases j <;> simp [γ0, γ1, Matrix.mul_apply, Fin.sum_univ_four]
  · ext i j; fin_cases i <;> fin_cases j <;> simp [γ0, γ2, Matrix.mul_apply, Fin.sum_univ_four]
  · ext i j; fin_cases i <;> fin_cases j <;> simp [γ0, γ3, Matrix.mul_apply, Fin.sum_univ_four]
  · ext i j; fin_cases i <;> fin_cases j <;> simp [γ1, γ2, Matrix.mul_apply, Fin.sum_univ_four]
  · ext i j; fin_cases i <;> fin_cases j <;> simp [γ1, γ3, Matrix.mul_apply, Fin.sum_univ_four]
  · ext i j; fin_cases i <;> fin_cases j <;> simp [γ2, γ3, Matrix.mul_apply, Fin.sum_univ_four]

/-- γ⁵ anticommutes with all γ^μ. -/
theorem γ5_anticomm_all :
    γ5 * γ0 + γ0 * γ5 = (0 : Matrix (Fin 4) (Fin 4) ℂ) ∧
    γ5 * γ1 + γ1 * γ5 = (0 : Matrix (Fin 4) (Fin 4) ℂ) ∧
    γ5 * γ2 + γ2 * γ5 = (0 : Matrix (Fin 4) (Fin 4) ℂ) ∧
    γ5 * γ3 + γ3 * γ5 = (0 : Matrix (Fin 4) (Fin 4) ℂ) := by
  unfold γ5
  refine ⟨?_, ?_, ?_, ?_⟩
  · ext i j; fin_cases i <;> fin_cases j <;>
      simp [γ0, γ1, γ2, γ3, Matrix.mul_apply, Fin.sum_univ_four, Complex.I_sq]
  · ext i j; fin_cases i <;> fin_cases j <;>
      simp [γ0, γ1, γ2, γ3, Matrix.mul_apply, Fin.sum_univ_four, Complex.I_sq]
  · ext i j; fin_cases i <;> fin_cases j <;>
      simp [γ0, γ1, γ2, γ3, Matrix.mul_apply, Fin.sum_univ_four, Complex.I_sq]
  · ext i j; fin_cases i <;> fin_cases j <;>
      simp [γ0, γ1, γ2, γ3, Matrix.mul_apply, Fin.sum_univ_four, Complex.I_sq]

end Section5
