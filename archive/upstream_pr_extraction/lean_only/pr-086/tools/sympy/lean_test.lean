import Mathlib.Data.Complex.Basic
import InfoGeometry.Clifford.DiracPauliGamma

open Matrix Complex InfoGeometry.Clifford.DiracPauliGamma

set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

noncomputable section

def hodgeStar (F : DiracMatrix) : DiracMatrix := -I • (gamma5 * F)

lemma gamma5_sq : gamma5 * gamma5 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
  simp [gamma5, gamma0, gamma1, gamma2, gamma3, Matrix.mul_apply, Fin.sum_univ_succ]

theorem hodgeStar_squared_eq_neg (F : DiracMatrix) : hodgeStar (hodgeStar F) = -F := by
  dsimp [hodgeStar]
  rw [Matrix.mul_smul, smul_smul]
  have h1 : (-I) * (-I) = -1 := by ring_nf; rw [I_sq]
  rw [h1, <- Matrix.mul_assoc, gamma5_sq, Matrix.one_mul, neg_one_smul]

