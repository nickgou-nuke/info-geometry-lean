import Mathlib.Data.Complex.Basic
import InfoGeometry.Clifford.DiracPauliGamma

open Matrix Complex InfoGeometry.Clifford.DiracPauliGamma

set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

noncomputable section

lemma gamma5_sq : gamma5 * gamma5 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
  simp [gamma5, Matrix.mul_apply, Fin.sum_univ_succ]

def P_SD : DiracMatrix := (1 / 2 : ℂ) • (1 + gamma5)
def P_ASD : DiracMatrix := (1 / 2 : ℂ) • (1 - gamma5)

theorem P_SD_idempotent : P_SD * P_SD = P_SD := by
  dsimp [P_SD]
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  have h1 : (1 / 2 : ℂ) * (1 / 2 : ℂ) = 1 / 4 := by ring
  rw [h1, Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, gamma5_sq]
  have h2 : (1 : DiracMatrix) * 1 + 1 * gamma5 + (gamma5 * 1 + 1) = (2 : ℂ) • (1 + gamma5) := by
    ext i j; simp [Matrix.add_apply, Matrix.mul_apply, smul_apply]; ring
  rw [h2, smul_smul]
  have h3 : (1 / 4 : ℂ) * 2 = 1 / 2 := by ring
  rw [h3]

theorem P_ASD_idempotent : P_ASD * P_ASD = P_ASD := by
  dsimp [P_ASD]
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  have h1 : (1 / 2 : ℂ) * (1 / 2 : ℂ) = 1 / 4 := by ring
  rw [h1, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, gamma5_sq]
  have h2 : (1 : DiracMatrix) * 1 - 1 * gamma5 - (gamma5 * 1 - 1) = (2 : ℂ) • (1 - gamma5) := by
    ext i j; simp [Matrix.sub_apply, Matrix.mul_apply, smul_apply]; ring
  rw [h2, smul_smul]
  have h3 : (1 / 4 : ℂ) * 2 = 1 / 2 := by ring
  rw [h3]

theorem P_SD_mul_P_ASD_eq_zero : P_SD * P_ASD = 0 := by
  dsimp [P_SD, P_ASD]
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  have h1 : (1 / 2 : ℂ) * (1 / 2 : ℂ) = 1 / 4 := by ring
  rw [h1, Matrix.add_mul, Matrix.mul_sub, Matrix.mul_sub, gamma5_sq]
  have h2 : (1 : DiracMatrix) * 1 - 1 * gamma5 + (gamma5 * 1 - 1) = 0 := by
    ext i j; simp [Matrix.add_apply, Matrix.sub_apply, Matrix.mul_apply, zero_apply]; try ring
  rw [h2, smul_zero]

