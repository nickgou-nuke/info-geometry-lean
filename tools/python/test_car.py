import os
import subprocess

def test_lean(code):
    with open("/home/goutev/repos/info-geometry-lean/test_car.lean", "w") as f:
        f.write(code)
    res = subprocess.run(["lake", "env", "lean", "test_car.lean"], cwd="/home/goutev/repos/info-geometry-lean", capture_output=True, text=True)
    return res

lean_code = """
import Mathlib
import InfoGeometry.Clifford.JordanWignerBridge

open scoped TensorProduct DirectSum Matrix Kronecker
open Matrix
open InfoGeometry.Clifford.Cl11TensorTower
open InfoGeometry.Clifford.JordanWignerBridge

lemma a_dagger_base_sq : a_dagger_base * a_dagger_base = 0 := by
  ext i j; fin_cases i <;> fin_cases j <;> norm_num [a_dagger_base, Matrix.mul_apply, Fin.sum_univ_two]

lemma a_base_sq : a_base * a_base = 0 := by
  ext i j; fin_cases i <;> fin_cases j <;> norm_num [a_base, Matrix.mul_apply, Fin.sum_univ_two]

lemma a_anticomm : a_dagger_base * a_base + a_base * a_dagger_base = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> norm_num [a_dagger_base, a_base, Matrix.mul_apply, Fin.sum_univ_two, Matrix.add_apply]

lemma gamma_chiral_base_sq : gamma_chiral_base * gamma_chiral_base = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> norm_num [gamma_chiral_base, gamma_0_base, gamma_1_base, InfoGeometry.Clifford.Cl11Matrix.J1, InfoGeometry.Clifford.Cl11Matrix.Eminus, Matrix.mul_apply, Fin.sum_univ_two]

lemma globalChirality_sq (k : ℕ) : globalChirality k * globalChirality k = 1 := by
  exact InfoGeometry.Clifford.TowerMatrix.Jn_sq gamma_chiral_base gamma_chiral_base_sq k

lemma jw_uv_anticomm_new (k : ℕ) : jw_u_new k * jw_v_new k + jw_v_new k * jw_u_new k = 1 := by
  unfold jw_u_new jw_v_new
  rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul]
  rw [globalChirality_sq]
  have h : (1 : MatStage k) ⊗ₖ (a_dagger_base * a_base) + (1 : MatStage k) ⊗ₖ (a_base * a_dagger_base) = (1 : MatStage k) ⊗ₖ (a_dagger_base * a_base + a_base * a_dagger_base) := by
    exact Matrix.kronecker_add_right (1 : MatStage k) (a_dagger_base * a_base) (a_base * a_dagger_base)
  rw [h, a_anticomm]
  ext i j
  simp
"""

res = test_lean(lean_code)
print("OUT:", res.stdout)
print("ERR:", res.stderr)
