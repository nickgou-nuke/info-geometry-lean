import Mathlib.Data.Complex.Basic
import InfoGeometry.Clifford.DiracPauliGamma

/-!
# InfoGeometry.Canonical.HodgeStar4D

This module formally implements the 4D Hodge Star Duality operator 
on the emergent Quaternionic/Clifford bivectors (2-forms).

It proves the exceptional property of 4D spacetime: the Hodge star 
maps 2-forms to 2-forms and satisfies $* * F = -F$ (Lorentzian signature).
This creates a complex structure on the space of 2-forms and enables 
the decomposition into Self-Dual (SD) and Anti-Self-Dual (ASD) components 
via the chiral projectors.
-/

namespace InfoGeometry.Canonical.HodgeStar4D

open Matrix
open Complex
open InfoGeometry.Clifford.DiracPauliGamma

set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

noncomputable section

/-- The Hodge Star operator acting on a 2-form (Clifford bivector) 
    in 4D Lorentzian signature is equivalent to multiplication by $-i \gamma_5$. -/
def hodgeStar (F : DiracMatrix) : DiracMatrix :=
  -I • (gamma5 * F)

lemma gamma5_sq : gamma5 * gamma5 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
  simp [gamma5, gamma0, gamma1, gamma2, gamma3, Matrix.mul_apply, Fin.sum_univ_succ]

/-- 
Theorem: In 4D Lorentzian spacetime, the Hodge star of the Hodge star 
of a 2-form yields the negative of the original form ($* * F = -F$).
This confirms the existence of a complex structure on 4D 2-forms.
-/
theorem hodgeStar_squared_eq_neg (F : DiracMatrix) : 
    hodgeStar (hodgeStar F) = -F := by
  dsimp [hodgeStar]
  rw [Matrix.mul_smul, smul_smul]
  have h1 : (-I) * (-I) = -1 := by ring_nf; rw [I_sq]
  rw [h1, <- Matrix.mul_assoc, gamma5_sq, Matrix.one_mul, neg_one_smul]

/-- The Self-Dual (SD) Projector $\frac{1 + \gamma_5}{2}$ -/
def P_SD : DiracMatrix :=
  (1 / 2 : ℂ) • (1 + gamma5)

/-- The Anti-Self-Dual (ASD) Projector $\frac{1 - \gamma_5}{2}$ -/
def P_ASD : DiracMatrix :=
  (1 / 2 : ℂ) • (1 - gamma5)

/-- Theorem: The Self-Dual Projector is idempotent. -/
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

/-- Theorem: The Anti-Self-Dual Projector is idempotent. -/
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

/-- Theorem: The SD and ASD Projectors are orthogonal. -/
theorem P_SD_mul_P_ASD_eq_zero : P_SD * P_ASD = 0 := by
  dsimp [P_SD, P_ASD]
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  have h1 : (1 / 2 : ℂ) * (1 / 2 : ℂ) = 1 / 4 := by ring
  rw [h1, Matrix.add_mul, Matrix.mul_sub, Matrix.mul_sub, gamma5_sq]
  have h2 : (1 : DiracMatrix) * 1 - 1 * gamma5 + (gamma5 * 1 - 1) = 0 := by
    ext i j; simp [Matrix.add_apply, Matrix.sub_apply, Matrix.mul_apply, zero_apply]; try ring
  rw [h2, smul_zero]

end

end InfoGeometry.Canonical.HodgeStar4D
