import Mathlib.LinearAlgebra.Matrix.Basic

open Matrix

namespace InfoGeometry.Algebra.SpinCore

/-- The 2-dimensional complex spin space canvas. -/
def SpinSpace : Type := Fin 2 → ℂ

/-- Chiral Raising Operator J₊ -/
def J_plus : Matrix (Fin 2) (Fin 2) ℂ :=
  !![0, 1;
     0, 0]

/-- Chiral Lowering Operator J₋ -/
def J_minus : Matrix (Fin 2) (Fin 2) ℂ :=
  !![0, 0;
     1, 0]

/-- Chiral Angular Momentum Operator J₀ -/
def J_zero : Matrix (Fin 2) (Fin 2) ℂ :=
  !![1, 0;
     0, -1]

/-- Theorem: Chiral Raising and Lowering operators are strict nilpotents. -/
theorem j_plus_nilpotent : J_plus * J_plus = 0 := by rfl
theorem j_minus_nilpotent : J_minus * J_minus = 0 := by rfl

end InfoGeometry.Algebra.SpinCore
