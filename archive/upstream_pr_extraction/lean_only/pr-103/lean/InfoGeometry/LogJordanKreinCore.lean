import Mathlib.Tactic

open Matrix

noncomputable section

namespace InfoGeometry.LogJordanKreinCore

def N : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; 0, 0]

def G : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; 1, 0]

def χ : Matrix (Fin 2) (Fin 2) ℝ := !![1, 0; 0, -1]

def scalarMatrix (Δ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  Matrix.diagonal fun _ : Fin 2 => Δ

def L (Δ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  scalarMatrix Δ + N

def expJordanCell (t Δ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  Real.exp (t * Δ) • (1 + t • N)

theorem jordanNilpotent_sq : N * N = 0 ∧ N ≠ 0 := by
  constructor
  · ext i j; fin_cases i <;> fin_cases j <;> simp [N, Matrix.mul_apply, Fin.sum_univ_two]
  · intro h
    have h01 := congr_fun (congr_fun h 0) 1
    simp [N] at h01

theorem jordanCell_krein_selfAdjoint (Δ : ℝ) :
    (L Δ).transpose * G = G * L Δ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [L, scalarMatrix, N, G, Matrix.transpose_apply, Matrix.mul_apply, Matrix.add_apply, Matrix.diagonal_apply, Fin.sum_univ_two]

theorem jordanCell_not_diagonalizable (Δ : ℝ) :
    ¬ (∃ (P : Matrix (Fin 2) (Fin 2) ℝ) (D : Matrix (Fin 2) (Fin 2) ℝ) (_ : Invertible P),
      (D 0 1 = 0 ∧ D 1 0 = 0) ∧ L Δ = P * D * ⅟P) := by
  intro ⟨P, D, _, ⟨hD01, hD10⟩, hL⟩
  have h_mul : L Δ * P = P * D := by
    rw [hL, Matrix.mul_assoc, invOf_mul_self, Matrix.mul_one]
  have h00 : (L Δ * P) 0 0 = (P * D) 0 0 := by rw [h_mul]
  have h01 : (L Δ * P) 0 1 = (P * D) 0 1 := by rw [h_mul]
  have h10 : (L Δ * P) 1 0 = (P * D) 1 0 := by rw [h_mul]
  have h11 : (L Δ * P) 1 1 = (P * D) 1 1 := by rw [h_mul]
  simp [L, scalarMatrix, N, hD01, hD10, Matrix.mul_apply, Fin.sum_univ_two] at h00 h01 h10 h11
  have hP10 : P 1 0 = 0 := by
    by_cases hD0 : Δ = D 0 0
    · subst hD0; linarith
    · have h_sub : (Δ - D 0 0) * P 1 0 = 0 := by linarith
      rcases mul_eq_zero.mp h_sub with h1 | h2
      · exfalso; exact hD0 (by linarith)
      · exact h2
  have hP11 : P 1 1 = 0 := by
    by_cases hD1 : Δ = D 1 1
    · subst hD1; linarith
    · have h_sub : (Δ - D 1 1) * P 1 1 = 0 := by linarith
      rcases mul_eq_zero.mp h_sub with h1 | h2
      · exfalso; exact hD1 (by linarith)
      · exact h2
  have h_det_zero : Matrix.det P = 0 := by
    simp [Matrix.det_fin_two, hP10, hP11]
  have h_det_unit : IsUnit (Matrix.det P) := Matrix.isUnit_det_of_invertible P
  have h_det_nonzero : Matrix.det P ≠ 0 := h_det_unit.ne_zero
  exact h_det_nonzero h_det_zero

theorem exp_jordanCell (t Δ : ℝ) :
    expJordanCell t Δ = !![Real.exp (t * Δ), t * Real.exp (t * Δ); 0, Real.exp (t * Δ)] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [expJordanCell, N, Matrix.smul_apply, Matrix.add_apply, mul_comm]

theorem trace_exp_jordanCell (t Δ : ℝ) :
    Matrix.trace (expJordanCell t Δ) = 2 * Real.exp (t * Δ) := by
  rw [exp_jordanCell]
  simp [Matrix.trace, Fin.sum_univ_two]
  ring

theorem detector_trace_jordanCell (t Δ : ℝ) :
    Matrix.trace (N.transpose * expJordanCell t Δ) = t * Real.exp (t * Δ) := by
  rw [exp_jordanCell]
  simp [N, Matrix.transpose_apply, Matrix.trace, Matrix.mul_apply, Fin.sum_univ_two]

theorem parity_trace_jordanCell (t Δ : ℝ) :
    Matrix.trace (χ * expJordanCell t Δ) = 0 := by
  rw [exp_jordanCell]
  simp [χ, Matrix.trace, Fin.sum_univ_two]

end InfoGeometry.LogJordanKreinCore
