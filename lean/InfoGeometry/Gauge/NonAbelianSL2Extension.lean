import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Topology.Instances.Complex
import Mathlib.Tactic

namespace InfoGeometry.Gauge.NonAbelianSL2Extension

open Complex Real Matrix

noncomputable section

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

def genJ : Matrix (Fin 2) (Fin 2) ℝ :=
  ![![0, -1],
    ![1, 0]]

def genK : Matrix (Fin 2) (Fin 2) ℝ :=
  ![![1, 0],
    ![0, -1]]

def genE : Matrix (Fin 2) (Fin 2) ℝ :=
  ![![0, 1],
    ![0, 0]]

def genF : Matrix (Fin 2) (Fin 2) ℝ :=
  ![![0, 0],
    ![1, 0]]

theorem genJ_sq_eq_neg_one :
    genJ * genJ = - 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [genJ, Matrix.mul_apply, Fin.sum_univ_two]

theorem genK_sq_eq_one :
    genK * genK = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [genK, Matrix.mul_apply, Fin.sum_univ_two]

theorem comm_K_E :
    genK * genE - genE * genK = (2 : ℝ) • genE := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [genK, genE, Matrix.mul_apply, Fin.sum_univ_two] <;> norm_num

theorem comm_K_F :
    genK * genF - genF * genK = -((2 : ℝ) • genF) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [genK, genF, Matrix.mul_apply, Fin.sum_univ_two] <;> norm_num

theorem comm_E_F :
    genE * genF - genF * genE = genK := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [genE, genF, genK, Matrix.mul_apply, Fin.sum_univ_two]
