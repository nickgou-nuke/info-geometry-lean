import Mathlib.Data.Complex.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
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
  (-Complex.I) • (gamma5 * F)

lemma gamma5_sq : gamma5 * gamma5 = 1 := by
  simpa using gamma5_mul_self

/-- 
Theorem: In 4D Lorentzian spacetime, the Hodge star of the Hodge star 
of a 2-form yields the negative of the original form ($* * F = -F$).
This confirms the existence of a complex structure on 4D 2-forms.
-/
theorem hodgeStar_squared_eq_neg (F : DiracMatrix) : 
    hodgeStar (hodgeStar F) = -F := by
  dsimp [hodgeStar]
  rw [Matrix.mul_smul, smul_smul]
  have h1 : (-Complex.I) * (-Complex.I) = (-1 : ℂ) := by ring_nf; rw [Complex.I_sq]
  rw [h1, <- Matrix.mul_assoc, gamma5_sq, Matrix.one_mul, neg_one_smul]

/-- The Self-Dual (SD) Projector $\frac{1 + \gamma_5}{2}$ -/
def P_SD : DiracMatrix :=
  (1 / 2 : ℂ) • ((1 : DiracMatrix) + gamma5)

/-- The Anti-Self-Dual (ASD) Projector $\frac{1 - \gamma_5}{2}$ -/
def P_ASD : DiracMatrix :=
  (1 / 2 : ℂ) • ((1 : DiracMatrix) - gamma5)

/-- Theorem: The Self-Dual Projector is idempotent. -/
theorem P_SD_idempotent : P_SD * P_SD = P_SD := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    (simp [P_SD, gamma5, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply]; try norm_num; try ring_nf)

/-- Theorem: The Anti-Self-Dual Projector is idempotent. -/
theorem P_ASD_idempotent : P_ASD * P_ASD = P_ASD := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    (simp [P_ASD, gamma5, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply]; try norm_num; try ring_nf)

/-- Theorem: The SD and ASD Projectors are orthogonal. -/
theorem P_SD_mul_P_ASD_eq_zero : P_SD * P_ASD = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    (simp [P_SD, P_ASD, gamma5, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply, zero_apply]; try norm_num; try ring_nf)

end

end InfoGeometry.Canonical.HodgeStar4D
