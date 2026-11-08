import Mathlib.Analysis.Calculus.Deriv.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
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
  change (∑ k : Fin 2, genJ i k * genJ k j) = (-1 : Matrix (Fin 2) (Fin 2) ℝ) i j
  fin_cases i <;> fin_cases j <;>
    norm_num [genJ, Matrix.one_apply, Fin.sum_univ_two]

theorem genK_sq_eq_one :
    genK * genK = 1 := by
  ext i j
  change (∑ k : Fin 2, genK i k * genK k j) = (1 : Matrix (Fin 2) (Fin 2) ℝ) i j
  fin_cases i <;> fin_cases j <;>
    norm_num [genK, Matrix.one_apply, Fin.sum_univ_two]

theorem comm_K_E :
    genK * genE - genE * genK = (2 : ℝ) • genE := by
  ext i j
  change (∑ k : Fin 2, genK i k * genE k j) -
      (∑ k : Fin 2, genE i k * genK k j) = 2 * genE i j
  fin_cases i <;> fin_cases j <;>
    norm_num [genK, genE, Fin.sum_univ_two]

theorem comm_K_F :
    genK * genF - genF * genK = -((2 : ℝ) • genF) := by
  ext i j
  change (∑ k : Fin 2, genK i k * genF k j) -
      (∑ k : Fin 2, genF i k * genK k j) = -(2 * genF i j)
  fin_cases i <;> fin_cases j <;>
    norm_num [genK, genF, Fin.sum_univ_two]

theorem comm_E_F :
    genE * genF - genF * genE = genK := by
  ext i j
  change (∑ k : Fin 2, genE i k * genF k j) -
      (∑ k : Fin 2, genF i k * genE k j) = genK i j
  fin_cases i <;> fin_cases j <;>
    norm_num [genE, genF, genK, Fin.sum_univ_two]
