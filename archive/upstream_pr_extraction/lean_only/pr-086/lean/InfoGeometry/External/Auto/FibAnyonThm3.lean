import Mathlib.Tactic
open Matrix
open Complex

noncomputable section

def R : Matrix (Fin 2) (Fin 2) ℂ :=
  !![Complex.exp (-4*Real.pi*Complex.I/5), 0; 0, Complex.exp (3*Real.pi*Complex.I/5)]

lemma conj_exp_pure_imag (θ : ℝ) : starRingEnd ℂ (Complex.exp (θ * Complex.I)) = Complex.exp (-θ * Complex.I) := by
  calc
    starRingEnd ℂ (Complex.exp (θ * Complex.I)) = Complex.exp (starRingEnd ℂ (θ * Complex.I)) := by rw [← Complex.exp_conj]
    _ = Complex.exp (θ * starRingEnd ℂ Complex.I) := by simp
    _ = Complex.exp (θ * (-Complex.I)) := by simp
    _ = Complex.exp (-θ * Complex.I) := by ring_nf

lemma starRingEnd_int (n : ℤ) : starRingEnd ℂ (n : ℂ) = (n : ℂ) := by simp

lemma starRingEnd_ofReal (x : ℝ) : starRingEnd ℂ (x : ℂ) = (x : ℂ) := Complex.conj_ofReal x

lemma conj_exp_neg4piI5 : starRingEnd ℂ (Complex.exp (-4*Real.pi*Complex.I/5)) = Complex.exp (4*Real.pi*Complex.I/5) := by
  calc
    starRingEnd ℂ (Complex.exp (-4*Real.pi*Complex.I/5)) = Complex.exp (starRingEnd ℂ (-4*Real.pi*Complex.I/5)) := by rw [← Complex.exp_conj]
    _ = Complex.exp (4*Real.pi*Complex.I/5) := by
      have h4 : starRingEnd ℂ (4 : ℂ) = (4 : ℂ) := by simpa using Complex.conj_ofReal (4 : ℝ)
      have h5 : starRingEnd ℂ (5 : ℂ) = (5 : ℂ) := by simpa using Complex.conj_ofReal (5 : ℝ)
      simp [Complex.conj_I, Complex.conj_ofReal, h4, h5]

lemma conj_exp_3piI5 : starRingEnd ℂ (Complex.exp (3*Real.pi*Complex.I/5)) = Complex.exp (-3*Real.pi*Complex.I/5) := by
  calc
    starRingEnd ℂ (Complex.exp (3*Real.pi*Complex.I/5)) = Complex.exp (starRingEnd ℂ (3*Real.pi*Complex.I/5)) := by rw [← Complex.exp_conj]
    _ = Complex.exp (-3*Real.pi*Complex.I/5) := by
      have h3 : starRingEnd ℂ (3 : ℂ) = (3 : ℂ) := by simpa using Complex.conj_ofReal (3 : ℝ)
      have h5 : starRingEnd ℂ (5 : ℂ) = (5 : ℂ) := by simpa using Complex.conj_ofReal (5 : ℝ)
      simp [Complex.conj_I, Complex.conj_ofReal, h3, h5]

theorem R_det : R.det = Complex.exp (-Real.pi*Complex.I/5) := by
  simp [R, Matrix.det_fin_two]
  rw [← Complex.exp_add]
  ring_nf

theorem R_unitary : R * Rᴴ = 1 := by
  ext i j; fin_cases i <;> fin_cases j
  · calc
      (R * Rᴴ) 0 0 = R 0 0 * Rᴴ 0 0 := by simp [Matrix.mul_apply, R]
      _ = Complex.exp (-4*Real.pi*Complex.I/5) * starRingEnd ℂ (Complex.exp (-4*Real.pi*Complex.I/5)) := by
        simp [R, Matrix.conjTranspose_apply]
      _ = Complex.exp (-4*Real.pi*Complex.I/5) * Complex.exp (4*Real.pi*Complex.I/5) := by rw [conj_exp_neg4piI5]
      _ = Complex.exp 0 := by
        rw [← Complex.exp_add, show (-4*Real.pi*Complex.I/5 + 4*Real.pi*Complex.I/5) = 0 by ring_nf, Complex.exp_zero]
      _ = 1 := by simp
      _ = (1 : Matrix (Fin 2) (Fin 2) ℂ) 0 0 := by simp
  · calc
      (R * Rᴴ) 0 1 = 0 := by simp [Matrix.mul_apply, R, Matrix.conjTranspose_apply]
      _ = (1 : Matrix (Fin 2) (Fin 2) ℂ) 0 1 := by simp
  · calc
      (R * Rᴴ) 1 0 = 0 := by simp [Matrix.mul_apply, R, Matrix.conjTranspose_apply]
      _ = (1 : Matrix (Fin 2) (Fin 2) ℂ) 1 0 := by simp
  · calc
      (R * Rᴴ) 1 1 = R 1 1 * Rᴴ 1 1 := by simp [Matrix.mul_apply, R]
      _ = Complex.exp (3*Real.pi*Complex.I/5) * starRingEnd ℂ (Complex.exp (3*Real.pi*Complex.I/5)) := by
        simp [R, Matrix.conjTranspose_apply]
      _ = Complex.exp (3*Real.pi*Complex.I/5) * Complex.exp (-3*Real.pi*Complex.I/5) := by rw [conj_exp_3piI5]
      _ = Complex.exp 0 := by
        rw [← Complex.exp_add, show (3*Real.pi*Complex.I/5 + (-3*Real.pi*Complex.I/5)) = 0 by ring_nf, Complex.exp_zero]
      _ = 1 := by simp
      _ = (1 : Matrix (Fin 2) (Fin 2) ℂ) 1 1 := by simp

end
