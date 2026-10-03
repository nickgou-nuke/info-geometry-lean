import Mathlib.Data.Real.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic

namespace InfoGeometry.GrandUnification.IwasawaDiracDecomposition

open Matrix

local notation "RealMat" => Matrix (Fin 2) (Fin 2) ℝ

-- The KAN Generators for sl(2, R)
def matOne : RealMat := !![1, 0; 0, 1]
def matI_R : RealMat := !![0, -1; 1, 0]  -- K (Compact, Angular)
def matJ_R : RealMat := !![1, 0; 0, -1]  -- A (Split, Scale)
def matN_R : RealMat := !![0, 1; 0, 0]   -- N (Nilpotent, Shear)

noncomputable def P_plus : RealMat := (1/2 : ℝ) • (matOne + matJ_R)
noncomputable def P_minus : RealMat := (1/2 : ℝ) • (matOne - matJ_R)

lemma mat_mul_expand (A B : RealMat) (i j : Fin 2) :
  (A * B) i j = A i 0 * B 0 j + A i 1 * B 1 j := by
  rw [Matrix.mul_apply, Fin.sum_univ_two]

-- 1. Local nilpotency of the horocyclic operator D_N (BRST/Koszul-like)
theorem D_N_sq : matN_R * matN_R = 0 := by
  ext i j
  fin_cases i
  all_goals fin_cases j
  all_goals {
    rw [mat_mul_expand]
    dsimp [matN_R]
    ring
  }

-- 2. The Dirac-Kähler Iwasawa Decomposition Theorem
-- Any traceless Dirac operator D uniquely decomposes into D_K + D_A + D_N
theorem iwasawa_dirac_decomposition (a b c : ℝ) :
  !![a, b; c, -a] = c • matI_R + a • matJ_R + (b + c) • matN_R := by
  ext i j
  fin_cases i
  all_goals fin_cases j
  all_goals {
    dsimp [matI_R, matJ_R, matN_R, Matrix.add_apply, Matrix.smul_apply]
    ring
  }

-- 3. The Scale Operator D_A acts as the spectral difference of the Peirce Polarization
theorem D_A_peirce_spectrum (a : ℝ) :
  a • matJ_R = a • P_plus - a • P_minus := by
  ext i j
  fin_cases i
  all_goals fin_cases j
  all_goals {
    dsimp [matJ_R, P_plus, P_minus, matOne, Matrix.sub_apply, Matrix.smul_apply, Matrix.add_apply]
    ring
  }

-- 4. The Horocyclic Operator D_N shears the Peirce Negative space into the Positive space
theorem D_N_shear_P_minus : matN_R * P_minus = matN_R := by
  ext i j
  fin_cases i
  all_goals fin_cases j
  all_goals {
    rw [mat_mul_expand]
    dsimp [matN_R, P_minus, matOne, matJ_R, Matrix.smul_apply, Matrix.sub_apply]
    ring
  }

theorem D_N_annihilate_P_plus : matN_R * P_plus = 0 := by
  ext i j
  fin_cases i
  all_goals fin_cases j
  all_goals {
    rw [mat_mul_expand]
    dsimp [matN_R, P_plus, matOne, matJ_R, Matrix.smul_apply, Matrix.add_apply]
    ring
  }

theorem P_plus_D_N_P_minus : P_plus * (matN_R * P_minus) = matN_R := by
  rw [D_N_shear_P_minus]
  ext i j
  fin_cases i
  all_goals fin_cases j
  all_goals {
    rw [mat_mul_expand]
    dsimp [matN_R, P_plus, matOne, matJ_R, Matrix.smul_apply, Matrix.add_apply]
    ring
  }

end InfoGeometry.GrandUnification.IwasawaDiracDecomposition
