import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Clifford.JordanWignerBridge

noncomputable section

open scoped TensorProduct DirectSum Matrix Kronecker
open Matrix
open InfoGeometry.Clifford.Cl11TensorTower
open InfoGeometry.Clifford.JordanWignerBridge

namespace InfoGeometry.Clifford.JordanWignerCAR

/-- Base creation operator squares to zero. -/
lemma a_dagger_base_sq : a_dagger_base * a_dagger_base = 0 := by
  ext i j; fin_cases i <;> fin_cases j <;> norm_num [a_dagger_base, Matrix.mul_apply, Fin.sum_univ_two]

/-- Base annihilation operator squares to zero. -/
lemma a_base_sq : a_base * a_base = 0 := by
  ext i j; fin_cases i <;> fin_cases j <;> norm_num [a_base, Matrix.mul_apply, Fin.sum_univ_two]

/-- Base anticommutator is the identity. -/
lemma a_anticomm : a_dagger_base * a_base + a_base * a_dagger_base = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> norm_num [a_dagger_base, a_base, Matrix.mul_apply, Fin.sum_univ_two, Matrix.add_apply]

/-- Base chiral volume element squares to identity. -/
lemma gamma_chiral_base_sq : gamma_chiral_base * gamma_chiral_base = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> norm_num [gamma_chiral_base, gamma_0_base, gamma_1_base, InfoGeometry.Clifford.Cl11Matrix.J1, InfoGeometry.Clifford.Cl11Matrix.Eminus, Matrix.mul_apply, Fin.sum_univ_two]

/-- Global chirality element squares to the identity at any stage. -/
lemma globalChirality_sq (k : ℕ) : globalChirality k * globalChirality k = 1 := by
  exact InfoGeometry.Clifford.TowerMatrix.Jn_sq gamma_chiral_base gamma_chiral_base_sq k

/--
GENUINE THEOREM: The single-site Jordan-Wigner creation operator squares to zero natively.
-/
theorem jw_u_new_sq (k : ℕ) : jw_u_new k * jw_u_new k = 0 := by
  unfold jw_u_new
  rw [← Matrix.mul_kronecker_mul]
  rw [globalChirality_sq, a_dagger_base_sq]
  ext i j
  simp

/--
GENUINE THEOREM: The single-site Jordan-Wigner annihilation operator squares to zero natively.
-/
theorem jw_v_new_sq (k : ℕ) : jw_v_new k * jw_v_new k = 0 := by
  unfold jw_v_new
  rw [← Matrix.mul_kronecker_mul]
  rw [globalChirality_sq, a_base_sq]
  ext i j
  simp

/--
GENUINE THEOREM: The single-site Jordan-Wigner creation and annihilation operators satisfy the CAR anticommutation relation {u, v} = 1 natively.
-/
theorem jw_uv_anticomm_new (k : ℕ) : jw_u_new k * jw_v_new k + jw_v_new k * jw_u_new k = 1 := by
  unfold jw_u_new jw_v_new
  rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul]
  rw [globalChirality_sq]
  have h_add : (1 : MatStage k) ⊗ₖ (a_dagger_base * a_base) + (1 : MatStage k) ⊗ₖ (a_base * a_dagger_base) = (1 : MatStage k) ⊗ₖ (a_dagger_base * a_base + a_base * a_dagger_base) := by
    ext i j
    simp [Matrix.add_apply]
    ring
  rw [h_add, a_anticomm]
  exact Matrix.one_kronecker_one (α := ℝ) (m := InfoGeometry.Clifford.TowerMatrix.Idx k) (n := Fin 2)

end InfoGeometry.Clifford.JordanWignerCAR
