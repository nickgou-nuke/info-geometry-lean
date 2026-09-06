import InfoGeometry.Lie.SplitOctonionEllCrossChannel
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

noncomputable section

namespace InfoGeometry.Lie.SplitOctonionEllProjective

open scoped Matrix

abbrev M₂ := Matrix (Fin 2) (Fin 2) ℝ

def H : M₂ := !![1, 0; 0, -1]

def E : M₂ := !![0, 1; 0, 0]

def F : M₂ := !![0, 0; 1, 0]

def uPlus : M₂ := !![1, 0; 0, 0]

def uMinus : M₂ := !![0, 0; 0, 1]

theorem H_sq : H * H = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [H, Matrix.mul_apply, Fin.sum_univ_two]

theorem E_sq : E * E = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [E, Matrix.mul_apply, Fin.sum_univ_two]

theorem F_sq : F * F = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [F, Matrix.mul_apply, Fin.sum_univ_two]

theorem E_mul_F : E * F = uPlus := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [E, F, uPlus, Matrix.mul_apply, Fin.sum_univ_two]

theorem F_mul_E : F * E = uMinus := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [E, F, uMinus, Matrix.mul_apply, Fin.sum_univ_two]

theorem uPlus_sq : uPlus * uPlus = uPlus := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [uPlus, Matrix.mul_apply, Fin.sum_univ_two]

theorem uMinus_sq : uMinus * uMinus = uMinus := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [uMinus, Matrix.mul_apply, Fin.sum_univ_two]

theorem uPlus_mul_uMinus : uPlus * uMinus = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [uPlus, uMinus, Matrix.mul_apply, Fin.sum_univ_two]

theorem uMinus_mul_uPlus : uMinus * uPlus = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [uPlus, uMinus, Matrix.mul_apply, Fin.sum_univ_two]

theorem uPlus_add_uMinus : uPlus + uMinus = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [uPlus, uMinus]

theorem uPlus_sub_uMinus : uPlus - uMinus = H := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [uPlus, uMinus, H]

theorem H_mul_E : H * E = E := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [H, E, Matrix.mul_apply, Fin.sum_univ_two]

theorem E_mul_H : E * H = -E := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [H, E, Matrix.mul_apply, Fin.sum_univ_two]

theorem H_mul_F : H * F = -F := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [H, F, Matrix.mul_apply, Fin.sum_univ_two]

theorem F_mul_H : F * H = F := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [H, F, Matrix.mul_apply, Fin.sum_univ_two]

theorem H_commutator_E : H * E - E * H = 2 • E := by
  rw [H_mul_E, E_mul_H]
  module

theorem H_commutator_F : H * F - F * H = -(2 • F) := by
  rw [H_mul_F, F_mul_H]
  module

theorem E_commutator_F : E * F - F * E = H := by
  rw [E_mul_F, F_mul_E, uPlus_sub_uMinus]

theorem E_anticommutator_F : E * F + F * E = 1 := by
  rw [E_mul_F, F_mul_E, uPlus_add_uMinus]

theorem uPlus_mul_E : uPlus * E = E := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [uPlus, E, Matrix.mul_apply, Fin.sum_univ_two]

theorem E_mul_uMinus : E * uMinus = E := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [E, uMinus, Matrix.mul_apply, Fin.sum_univ_two]

theorem uMinus_mul_F : uMinus * F = F := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [uMinus, F, Matrix.mul_apply, Fin.sum_univ_two]

theorem F_mul_uPlus : F * uPlus = F := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [F, uPlus, Matrix.mul_apply, Fin.sum_univ_two]

theorem uMinus_mul_E : uMinus * E = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [uMinus, E, Matrix.mul_apply, Fin.sum_univ_two]

theorem E_mul_uPlus : E * uPlus = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [E, uPlus, Matrix.mul_apply, Fin.sum_univ_two]

theorem uPlus_mul_F : uPlus * F = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [uPlus, F, Matrix.mul_apply, Fin.sum_univ_two]

theorem F_mul_uMinus : F * uMinus = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [F, uMinus, Matrix.mul_apply, Fin.sum_univ_two]

theorem projectiveRay_plus_fixed (z : ℝ) :
    uPlus *ᵥ ![z, 0] = ![z, 0] := by
  funext i
  fin_cases i <;>
    simp [uPlus, Matrix.mulVec, Matrix.mul_apply, dotProduct, Fin.sum_univ_two]

theorem projectiveRay_minus_fixed (z : ℝ) :
    uMinus *ᵥ ![0, z] = ![0, z] := by
  funext i
  fin_cases i <;>
    simp [uMinus, Matrix.mulVec, Matrix.mul_apply, dotProduct, Fin.sum_univ_two]

theorem H_ne_one : H ≠ 1 := by
  intro h
  have hentry := congr_fun (congr_fun h (1 : Fin 2)) (1 : Fin 2)
  norm_num [H] at hentry

theorem H_mul_plus_ray (z : ℝ) :
    H *ᵥ ![z, 0] = ![z, 0] := by
  funext i
  fin_cases i <;>
    simp [H, Matrix.mulVec, Matrix.mul_apply, dotProduct, Fin.sum_univ_two]

theorem H_mul_minus_ray (z : ℝ) :
    H *ᵥ ![0, z] = -![0, z] := by
  funext i
  fin_cases i <;>
    simp [H, Matrix.mulVec, Matrix.mul_apply, dotProduct, Fin.sum_univ_two]

end InfoGeometry.Lie.SplitOctonionEllProjective
