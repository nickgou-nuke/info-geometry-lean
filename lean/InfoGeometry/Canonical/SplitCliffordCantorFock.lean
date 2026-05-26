import Mathlib

/-!
# InfoGeometry.Canonical.SplitCliffordCantorFock

Boolean/Cantor local encoding of the `2×2` split-Clifford ladder block.
-/

namespace InfoGeometry.Canonical.SplitCliffordCantorFock

open Matrix

abbrev M2R := Matrix (Fin 2) (Fin 2) ℝ
abbrev V2R := Matrix (Fin 2) (Fin 1) ℝ

/-- `false` (empty) local basis state `|0⟩`. -/
def state_false : V2R := !![1; 0]

/-- `true` (occupied) local basis state `|1⟩`. -/
def state_true : V2R := !![0; 1]

/-- Boolean-to-state map. -/
def cantorState (b : Bool) : V2R :=
  if b then state_true else state_false

/-- Local annihilation operator. -/
def a_op : M2R := !![0, 1; 0, 0]

/-- Local creation operator. -/
def aDag_op : M2R := !![0, 0; 1, 0]

/-- Local number operator. -/
def num_op : M2R := aDag_op * a_op

/-- Creation maps `false` to `true`. -/
theorem create_false_eq_true :
    aDag_op * cantorState false = cantorState true := by
  unfold cantorState state_false state_true aDag_op
  ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.mul_apply, Fin.sum_univ_two]

/-- Annihilation maps `true` to `false`. -/
theorem annihilate_true_eq_false :
    a_op * cantorState true = cantorState false := by
  unfold cantorState state_false state_true a_op
  ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.mul_apply, Fin.sum_univ_two]

/-- Creation annihilates `true` (Pauli exclusion). -/
theorem create_true_eq_zero :
    aDag_op * cantorState true = 0 := by
  unfold cantorState state_true aDag_op
  ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.mul_apply, Fin.sum_univ_two]

/-- Annihilation annihilates `false`. -/
theorem annihilate_false_eq_zero :
    a_op * cantorState false = 0 := by
  unfold cantorState state_false a_op
  ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.mul_apply, Fin.sum_univ_two]

/-- Number operator reads `true` with eigenvalue `1`. -/
theorem num_op_true_eval :
    num_op * cantorState true = cantorState true := by
  unfold num_op
  rw [Matrix.mul_assoc, annihilate_true_eq_false, create_false_eq_true]

/-- Number operator reads `false` with eigenvalue `0`. -/
theorem num_op_false_eval :
    num_op * cantorState false = 0 := by
  unfold num_op
  rw [Matrix.mul_assoc, annihilate_false_eq_zero, Matrix.mul_zero]

end InfoGeometry.Canonical.SplitCliffordCantorFock
