import Mathlib.Tactic
open Matrix
open Real

noncomputable section

/-! Theorem 2: F-Matrix -/

def φ : ℝ := (1 + Real.sqrt 5) / 2

lemma h5sq : (Real.sqrt 5)^2 = (5 : ℝ) :=
  Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)

lemma golden : φ^2 = φ + 1 := by
  dsimp [φ]
  calc
    ((1 + Real.sqrt 5) / 2)^2 = ((1 + Real.sqrt 5)^2) / 4 := by ring_nf
    _ = (1 + 2*Real.sqrt 5 + (Real.sqrt 5)^2) / 4 := by ring_nf
    _ = (1 + 2*Real.sqrt 5 + 5) / 4 := by rw [h5sq]
    _ = (6 + 2*Real.sqrt 5) / 4 := by ring_nf
    _ = (3 + Real.sqrt 5) / 2 := by ring_nf
    _ = (1 + Real.sqrt 5) / 2 + 1 := by ring_nf

lemma φ_pos : φ > 0 := by
  dsimp [φ]
  have h5pos : Real.sqrt 5 > 0 := Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 5)
  nlinarith

lemma φ_ne_zero : φ ≠ 0 := by linarith [φ_pos]

lemma sqrt_φ_sq : (Real.sqrt φ)^2 = φ :=
  Real.sq_sqrt (by linarith [φ_pos])

lemma sqrt_φ_ne_zero : Real.sqrt φ ≠ 0 :=
  (Real.sqrt_pos.mpr φ_pos).ne.symm

lemma inv_phi_sq_plus_inv_phi : (1/φ)^2 + 1/φ = 1 := by
  field_simp [φ_ne_zero]
  nlinarith [golden]

def F : Matrix (Fin 2) (Fin 2) ℝ :=
  !![1/φ, 1 / Real.sqrt φ; 1 / Real.sqrt φ, -1/φ]

theorem F_sq_eq_I : F * F = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [F, Matrix.mul_apply] <;>
    field_simp [φ_ne_zero, sqrt_φ_ne_zero] <;>
    simp [sqrt_φ_sq] <;>
    nlinarith [golden]

theorem F_det : F.det = -1 := by
  simp [F, Matrix.det_fin_two]
  field_simp [φ_ne_zero, sqrt_φ_ne_zero]
  simp [sqrt_φ_sq]
  nlinarith [golden]

end
