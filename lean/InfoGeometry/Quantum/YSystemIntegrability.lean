import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Topology.Instances.Complex
import Mathlib.Tactic

namespace InfoGeometry.Quantum.YSystemIntegrability

open Complex Real

noncomputable section

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

def incMatrixA1 : Matrix (Fin 1) (Fin 1) ℕ :=
  !![0]

def incMatrixA2 : Matrix (Fin 2) (Fin 2) ℕ :=
  ![![0, 1],
    ![1, 0]]

def yFunctionOfEnergy (ε : ℝ) : ℝ :=
  Real.exp (-ε)

def ySystemRhsA1 (Y : ℝ) : ℝ :=
  (1 + Y) ^ 0

def ySystemRhsA2 (Y_other : ℝ) : ℝ :=
  1 + Y_other

theorem y_function_pos (ε : ℝ) :
    0 < yFunctionOfEnergy ε := by
  unfold yFunctionOfEnergy
  exact Real.exp_pos (-ε)

theorem y_system_term_gt_one (ε : ℝ) :
    1 < 1 + yFunctionOfEnergy ε := by
  have h := y_function_pos ε
  linarith

theorem y_system_a1_rhs_eq_one (Y : ℝ) :
    ySystemRhsA1 Y = 1 := by
  unfold ySystemRhsA1
  ring

theorem inc_matrix_a2_symmetric :
    incMatrixA2 0 1 = 1 ∧ incMatrixA2 1 0 = 1 := by
  unfold incMatrixA2
  refine ⟨rfl, rfl⟩

theorem y_system_a1_phase_product (φ : ℝ) :
    (Complex.exp (-Complex.I * (φ : ℂ))) * (Complex.exp (Complex.I * (φ : ℂ))) = 1 := by
  rw [← Complex.exp_add]
  have : -Complex.I * (φ : ℂ) + Complex.I * (φ : ℂ) = 0 := by ring
  rw [this, Complex.exp_zero]

def coxeterNumberA1 : ℕ := 2

def zamolodchikovPeriodUnitsA1 : ℕ :=
  coxeterNumberA1 + 2

theorem zamolodchikov_period_a1_eval :
    zamolodchikovPeriodUnitsA1 = 4 := by
  unfold zamolodchikovPeriodUnitsA1 coxeterNumberA1
  rfl
