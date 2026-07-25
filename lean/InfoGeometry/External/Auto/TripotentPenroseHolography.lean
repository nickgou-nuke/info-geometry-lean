import Mathlib.Tactic

/-!
# Tripotent operators and Penrose inflation

Repaired external file: concrete tripotent matrix plus trace/determinant of the
Fibonacci/Penrose inflation matrix.
-/

noncomputable section

namespace TripotentPenrose

open Matrix

/-- An algebraic element is tripotent if it equals its own cube. -/
def IsTripotent {R : Type} [Ring R] (T : R) : Prop := T * T * T = T

/-- Standard `3×3` tripotent with eigenvalues `1,-1,0`. -/
def T_zero : Matrix (Fin 3) (Fin 3) ℝ := !![1, 0, 0; 0, -1, 0; 0, 0, 0]

/-- `T_zero³=T_zero`. -/
theorem T_zero_is_tripotent : IsTripotent T_zero := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [IsTripotent, T_zero, Matrix.mul_apply, Fin.sum_univ_three]

/-- Fibonacci/Penrose inflation matrix. -/
def PenroseInflation : Matrix (Fin 2) (Fin 2) ℝ := !![1, 1; 1, 0]

/-- Trace of the inflation matrix. -/
theorem penrose_trace : Matrix.trace PenroseInflation = 1 := by
  simp [PenroseInflation, Matrix.trace, Matrix.diag, Fin.sum_univ_two]

/-- Determinant of the inflation matrix. -/
theorem penrose_det : PenroseInflation.det = -1 := by
  simp [PenroseInflation, Matrix.det_fin_two]

#check T_zero_is_tripotent
#check penrose_trace
#check penrose_det

end TripotentPenrose
