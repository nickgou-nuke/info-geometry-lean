import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# SL(2,ℝ) Modular Flow Matrix Algebra

This module formalizes the infinitesimal modular flow as an action of SL(2,ℝ)
matrices. It avoids abstract topological groups and works directly with native
Mathlib 2x2 matrices over the reals.
-/

namespace InfoGeometry.OperatorAlgebra.SL2R

/-- The Lie algebra sl(2,ℝ) represented as 2x2 traceless real matrices. -/
def sl2R (M : Matrix (Fin 2) (Fin 2) ℝ) : Prop :=
  Matrix.trace M = 0

/-- The standard modular flow generator L₀. -/
def L0 : Matrix (Fin 2) (Fin 2) ℝ :=
  ![![1, 0],
    ![0, -1]]

theorem L0_is_sl2R : sl2R L0 := by
  unfold sl2R
  simp [L0, Matrix.trace]

/-- The modular evolution generator L₁ (raising operator analog). -/
def L1 : Matrix (Fin 2) (Fin 2) ℝ :=
  ![![0, 1],
    ![0, 0]]

theorem L1_is_sl2R : sl2R L1 := by
  unfold sl2R
  simp [L1, Matrix.trace]

/-- The modular evolution generator L₋₁ (lowering operator analog). -/
def L_minus_1 : Matrix (Fin 2) (Fin 2) ℝ :=
  ![![0, 0],
    ![1, 0]]

theorem L_minus_1_is_sl2R : sl2R L_minus_1 := by
  unfold sl2R
  simp [L_minus_1, Matrix.trace]

/-- The standard commutation relation [L1, L₋₁] = L₀. -/
theorem commutator_L1_L_minus_1 : L1 * L_minus_1 - L_minus_1 * L1 = L0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [L1, L_minus_1, L0, Matrix.mul_apply, Matrix.sub_apply, Fin.sum_univ_two, Matrix.vecHead, Matrix.vecTail]

end InfoGeometry.OperatorAlgebra.SL2R
