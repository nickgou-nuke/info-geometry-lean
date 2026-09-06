import Mathlib.Tactic

/-!
# Liu--Collins affine invariance finite matrix facts

Repair of the external file: `C₂=-I` commutes with every `2×2` real matrix, and
an axis reflection commutes with diagonal parallel/perpendicular scaling.
-/

noncomputable section

namespace LiuCollins

open Matrix

abbrev M2R := Matrix (Fin 2) (Fin 2) ℝ

/-- The `C₂` half-turn matrix. -/
def C2 : M2R := !![-1, 0; 0, -1]

/-- Since `C₂=-I`, it commutes with every linear affine part. -/
theorem C2_commutes_all_affine (A : M2R) : A * C2 = C2 * A := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [C2, Matrix.mul_apply, Fin.sum_univ_two]

/-- Reflection across the x-axis. -/
def Rx : M2R := !![1, 0; 0, -1]

/-- Non-uniform diagonal scaling. -/
def Scale (sx sy : ℝ) : M2R := !![sx, 0; 0, sy]

/-- Axis reflection commutes with diagonal scaling in parallel/perpendicular axes. -/
theorem Rx_commutes_scaling (sx sy : ℝ) : Scale sx sy * Rx = Rx * Scale sx sy := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [Rx, Scale, Matrix.mul_apply, Fin.sum_univ_two]

#check C2_commutes_all_affine
#check Rx_commutes_scaling

end LiuCollins
