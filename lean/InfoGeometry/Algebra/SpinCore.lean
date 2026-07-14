import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Algebra.BigOperators.Fin

open Matrix

namespace SpinCore

/-- The 2-dimensional rational spin space canvas. -/
def SpinSpace : Type := Fin 2 → ℚ

/-- Chiral Raising Operator J₊ -/
def J_plus : Matrix (Fin 2) (Fin 2) ℚ :=
  ![![0, 1], ![0, 0]]

/-- Chiral Lowering Operator J₋ -/
def J_minus : Matrix (Fin 2) (Fin 2) ℚ :=
  ![![0, 0], ![1, 0]]

/-- Chiral Angular Momentum Operator J₀ -/
def J_zero : Matrix (Fin 2) (Fin 2) ℚ :=
  ![![1, 0], ![0, -1]]

/-- Theorem: Chiral Raising and Lowering operators are strict nilpotents. -/
theorem j_plus_nilpotent : J_plus * J_plus = 0 := by ext i j; fin_cases i <;> fin_cases j <;> simp [J_plus, mul_apply, Fin.sum_univ_two]
theorem j_minus_nilpotent : J_minus * J_minus = 0 := by ext i j; fin_cases i <;> fin_cases j <;> simp [J_minus, mul_apply, Fin.sum_univ_two]

end SpinCore
