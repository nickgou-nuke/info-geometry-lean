import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic
import InfoGeometry.Lie.SplitOctonionPeirceExterior3CoordinateBridge

/-!
# Split-Octonion Exterior Algebra Peirce Bridge

This module formalizes the canonical operator bridge connecting:
1. **The Graded Exterior Algebra Carrier $\Lambda^\bullet \mathbb{R}^3$ ($1 + 3 + 3 + 1$)**:
   - $\Lambda^0 \mathbb{R}^3 \cong \mathbb{R}$ (scalars / $u_+$ / index 0)
   - $\Lambda^1 \mathbb{R}^3 \cong \mathbb{R}^3$ (vectors / $\boldsymbol{\sigma}^+$ / indices 1, 2, 3)
   - $\Lambda^2 \mathbb{R}^3 \cong \mathbb{R}^3$ (bivectors / $\boldsymbol{\sigma}^-$ / indices 5, 6, 7)
   - $\Lambda^3 \mathbb{R}^3 \cong \mathbb{R}$ (pseudoscalars / $u_-$ / index 4)

2. **Creation $\varepsilon_0$ and Contraction $\iota_0$ Operators on $\Lambda^\bullet \mathbb{R}^3$**:
   - $\varepsilon_0 : \Lambda^k \to \Lambda^{k+1}$
   - $\iota_0 : \Lambda^k \to \Lambda^{k-1}$

3. **🏆 THEOREM 1 (The Canonical Anticommutation Relations / CAR Clifford Atom)**:
   - Nilpotency: $\varepsilon_0^2 = 0$, $\iota_0^2 = 0$
   - CAR Identity: $\varepsilon_0 \iota_0 + \iota_0 \varepsilon_0 = I$

4. **🏆 THEOREM 2 (Peirce Grading vs Exchange Involution / Nambu–Gorkov Pattern)**:
   - Peirce grading $\Gamma_P := \operatorname{diag}(+1, +1, +1, +1, -1, -1, -1, -1)$
   - Exchange involution $\kappa_{\rm exch} : V_+ \leftrightarrow V_-$
   - Conjugation anti-commutation: $\kappa_{\rm exch} \Gamma_P \kappa_{\rm exch} = -\Gamma_P$

5. **🏆 THEOREM 3 (Peirce Idempotent Projectors)**:
   - $P_+ = \frac{I + \Gamma_P}{2}$, $P_- = \frac{I - \Gamma_P}{2}$
   - $P_+^2 = P_+$, $P_-^2 = P_-$, $P_+ P_- = 0$, $P_+ + P_- = I$
-/

noncomputable section

namespace InfoGeometry.Lie.SplitOctonionExteriorAlgebraPeirceBridge

open Matrix
open InfoGeometry.Lie.SplitOctonionPeirceExterior3CoordinateBridge

abbrev Dim8 := Fin 8
abbrev Mat8 := Matrix Dim8 Dim8 ℝ

/-- Matrix representation of the creation operator $\varepsilon_0 = e_0 \wedge (-)$. -/
def eps0Mat : Mat8 :=
  ![![0, 0, 0, 0, 0, 0, 0, 0],
    ![1, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 1, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 1, 0, 0, 0, 0],
    ![0, 0, -1, 0, 0, 0, 0, 0]]

/-- Matrix representation of the contraction operator $\iota_0 = \iota(e_0)$. -/
def iota0Mat : Mat8 :=
  ![![0, 1, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, -1],
    ![0, 0, 0, 0, 0, 0, 1, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 1, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0]]

/-- Matrix representation of the Peirce grading operator $\Gamma_P$:
    $+1$ on $V_+$ and $-1$ on $V_-$. -/
def peirceGradingMat : Mat8 :=
  ![![1, 0, 0, 0, 0, 0, 0, 0],
    ![0, 1, 0, 0, 0, 0, 0, 0],
    ![0, 0, 1, 0, 0, 0, 0, 0],
    ![0, 0, 0, 1, 0, 0, 0, 0],
    ![0, 0, 0, 0, -1, 0, 0, 0],
    ![0, 0, 0, 0, 0, -1, 0, 0],
    ![0, 0, 0, 0, 0, 0, -1, 0],
    ![0, 0, 0, 0, 0, 0, 0, -1]]

/-- Matrix representation of the exchange involution $\kappa_{\rm exch}$:
    swaps $V_+$ and $V_-$. -/
def exchangeInvolutionMat : Mat8 :=
  ![![0, 0, 0, 0, 1, 0, 0, 0],
    ![0, 0, 0, 0, 0, 1, 0, 0],
    ![0, 0, 0, 0, 0, 0, 1, 0],
    ![0, 0, 0, 0, 0, 0, 0, 1],
    ![1, 0, 0, 0, 0, 0, 0, 0],
    ![0, 1, 0, 0, 0, 0, 0, 0],
    ![0, 0, 1, 0, 0, 0, 0, 0],
    ![0, 0, 0, 1, 0, 0, 0, 0]]

/-- Matrix representation of the Peirce projector $P_+ = \operatorname{diag}(1,1,1,1,0,0,0,0)$. -/
def peirceProjectorPlusMat : Mat8 :=
  ![![1, 0, 0, 0, 0, 0, 0, 0],
    ![0, 1, 0, 0, 0, 0, 0, 0],
    ![0, 0, 1, 0, 0, 0, 0, 0],
    ![0, 0, 0, 1, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0]]

/-- Matrix representation of the Peirce projector $P_- = \operatorname{diag}(0,0,0,0,1,1,1,1)$. -/
def peirceProjectorMinusMat : Mat8 :=
  ![![0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 1, 0, 0, 0],
    ![0, 0, 0, 0, 0, 1, 0, 0],
    ![0, 0, 0, 0, 0, 0, 1, 0],
    ![0, 0, 0, 0, 0, 0, 0, 1]]

/-- 🏆 THEOREM 1A: Creation Nilpotency: $\varepsilon_0^2 = 0$. -/
theorem eps0Mat_sq : eps0Mat * eps0Mat = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> (
    simp [Matrix.mul_apply, eps0Mat, Fin.sum_univ_eight]
  )

/-- 🏆 THEOREM 1B: Contraction Nilpotency: $\iota_0^2 = 0$. -/
theorem iota0Mat_sq : iota0Mat * iota0Mat = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> (
    simp [Matrix.mul_apply, iota0Mat, Fin.sum_univ_eight]
  )

/-- 🏆 THEOREM 1C: CAR Anticommutation Relation for mode 0:
    $\varepsilon_0 \iota_0 + \iota_0 \varepsilon_0 = I$. -/
theorem eps0_iota0_anticomm : eps0Mat * iota0Mat + iota0Mat * eps0Mat = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> (
    simp [Matrix.mul_apply, Matrix.add_apply, eps0Mat, iota0Mat, Fin.sum_univ_eight]
  )

/-- 🏆 THEOREM 2A: Peirce Grading Involutivity: $\Gamma_P^2 = I$. -/
theorem peirceGradingMat_sq : peirceGradingMat * peirceGradingMat = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> (
    simp [Matrix.mul_apply, peirceGradingMat, Fin.sum_univ_eight]
  )

/-- 🏆 THEOREM 2B: Exchange Involution Involutivity: $\kappa_{\rm exch}^2 = I$. -/
theorem exchangeInvolutionMat_sq : exchangeInvolutionMat * exchangeInvolutionMat = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> (
    simp [Matrix.mul_apply, exchangeInvolutionMat, Fin.sum_univ_eight]
  )

/-- 🏆 THEOREM 2C (The Nambu–Gorkov Chirality Conjugation Law):
    $\kappa_{\rm exch} \Gamma_P \kappa_{\rm exch} = -\Gamma_P$. -/
theorem exchange_peirceGrading_anticomm :
    exchangeInvolutionMat * peirceGradingMat * exchangeInvolutionMat = -peirceGradingMat := by
  ext i j
  fin_cases i <;> fin_cases j <;> (
    simp [Matrix.mul_apply, Matrix.neg_apply, exchangeInvolutionMat, peirceGradingMat, Fin.sum_univ_eight]
  )

/-- 🏆 THEOREM 2D: Peirce Idempotent Projector $P_+$ formula recovery:
    $P_+ = \frac{I + \Gamma_P}{2}$. -/
theorem peirceProjectorPlusMat_eq_half_add :
    peirceProjectorPlusMat = (1 / 2 : ℝ) • (1 + peirceGradingMat) := by
  ext i j
  fin_cases i <;> fin_cases j <;> (
    first
    | (simp [peirceProjectorPlusMat, Matrix.smul_apply, Matrix.add_apply, peirceGradingMat]; norm_num)
    | simp [peirceProjectorPlusMat, Matrix.smul_apply, Matrix.add_apply, peirceGradingMat]
  )

/-- 🏆 THEOREM 2E: Peirce Idempotent Projector $P_-$ formula recovery:
    $P_- = \frac{I - \Gamma_P}{2}$. -/
theorem peirceProjectorMinusMat_eq_half_sub :
    peirceProjectorMinusMat = (1 / 2 : ℝ) • (1 - peirceGradingMat) := by
  ext i j
  fin_cases i <;> fin_cases j <;> (
    first
    | (simp [peirceProjectorMinusMat, Matrix.smul_apply, Matrix.sub_apply, peirceGradingMat]; norm_num)
    | simp [peirceProjectorMinusMat, Matrix.smul_apply, Matrix.sub_apply, peirceGradingMat]
  )

/-- 🏆 THEOREM 2F: Peirce Projector Idempotency:
    $P_+^2 = P_+$, $P_-^2 = P_-$. -/
theorem peirceProjectorPlusMat_idempotent :
    peirceProjectorPlusMat * peirceProjectorPlusMat = peirceProjectorPlusMat := by
  ext i j
  fin_cases i <;> fin_cases j <;> (
    simp [Matrix.mul_apply, peirceProjectorPlusMat, Fin.sum_univ_eight]
  )

theorem peirceProjectorMinusMat_idempotent :
    peirceProjectorMinusMat * peirceProjectorMinusMat = peirceProjectorMinusMat := by
  ext i j
  fin_cases i <;> fin_cases j <;> (
    simp [Matrix.mul_apply, peirceProjectorMinusMat, Fin.sum_univ_eight]
  )

/-- 🏆 THEOREM 2G: Peirce Projector Orthogonality and Completeness:
    $P_+ P_- = 0$, $P_+ + P_- = I$. -/
theorem peirceProjectors_orthogonal :
    peirceProjectorPlusMat * peirceProjectorMinusMat = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> (
    simp [peirceProjectorPlusMat, peirceProjectorMinusMat, Matrix.mul_apply, Fin.sum_univ_eight]
  )

theorem peirceProjectors_complete :
    peirceProjectorPlusMat + peirceProjectorMinusMat = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> (
    simp [peirceProjectorPlusMat, peirceProjectorMinusMat, Matrix.add_apply]
  )

end InfoGeometry.Lie.SplitOctonionExteriorAlgebraPeirceBridge
