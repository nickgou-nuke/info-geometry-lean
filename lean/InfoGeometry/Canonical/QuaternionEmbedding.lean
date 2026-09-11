import Mathlib.Data.Complex.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Algebra.Star.Basic
import InfoGeometry.Clifford.DiracPauliGamma

noncomputable section

namespace InfoGeometry.Canonical.QuaternionEmbedding

open Complex InfoGeometry.Clifford.DiracPauliGamma

/-!
# Quaternion Embedding into Clifford Algebra

Embeds the quaternion algebra H into Cl(1,3;C) via the bivector construction.
The quaternions are identified with the spatial bivectors of Cl(1,3).

Key isomorphism: H ≅ Cl(0,2) ⊂ Cl(1,3;C) via spatial bivectors.
-/

/-- Quaternion basis elements as Dirac bivectors.
    i ↦ γ²γ³, j ↦ γ³γ¹, k ↦ γ¹γ²
    These satisfy i² = j² = k² = -I and ij = k, jk = i, ki = j. -/
def quat_i : DiracMatrix := gamma2 * gamma3
def quat_j : DiracMatrix := gamma3 * gamma1
def quat_k : DiracMatrix := gamma1 * gamma2

/-- Quaternion basis element i squares to -I. -/
theorem quat_i_sq : quat_i * quat_i = -1 := by
  unfold quat_i
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [gamma2, gamma3, Matrix.mul_apply, Fin.sum_univ_succ, Complex.I_mul_I]

/-- Quaternion basis element j squares to -I. -/
theorem quat_j_sq : quat_j * quat_j = -1 := by
  unfold quat_j
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [gamma3, gamma1, Matrix.mul_apply, Fin.sum_univ_succ]

/-- Quaternion basis element k squares to -I. -/
theorem quat_k_sq : quat_k * quat_k = -1 := by
  unfold quat_k
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [gamma1, gamma2, Matrix.mul_apply, Fin.sum_univ_succ, Complex.I_mul_I]

/-- Quaternion relation: i*j = k. -/
theorem quat_ij_eq_k : quat_i * quat_j = quat_k := by
  unfold quat_i quat_j quat_k
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [gamma1, gamma2, gamma3, Matrix.mul_apply, Fin.sum_univ_succ]

/-- Quaternion relation: j*k = i. -/
theorem quat_jk_eq_i : quat_j * quat_k = quat_i := by
  unfold quat_i quat_j quat_k
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [gamma1, gamma2, gamma3, Matrix.mul_apply, Fin.sum_univ_succ]

/-- Quaternion relation: k*i = j. -/
theorem quat_ki_eq_j : quat_k * quat_i = quat_j := by
  unfold quat_i quat_j quat_k
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [gamma1, gamma2, gamma3, Matrix.mul_apply, Fin.sum_univ_succ, Complex.I_mul_I]

/-- Quaternion relation: i*j*k = -I. -/
theorem quat_ijk_eq_neg_one : quat_i * quat_j * quat_k = -1 := by
  calc
    quat_i * quat_j * quat_k = (quat_i * quat_j) * quat_k := rfl
    _ = quat_k * quat_k := by rw [quat_ij_eq_k]
    _ = -1 := quat_k_sq

/-- The quaternion algebra H embeds into Cl(1,3;C) as the even subalgebra. -/
def quaternionToClifford (a b c d : ℂ) : DiracMatrix :=
  a • 1 + b • quat_i + c • quat_j + d • quat_k

end InfoGeometry.Canonical.QuaternionEmbedding
