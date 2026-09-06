import InfoGeometry.Quantum.QuaternionSpinTimeReversal

open InfoGeometry.Topology.Q8MonodromySpinorCover
open InfoGeometry.Quantum.QuaternionSpinTimeReversal

private theorem zmod4_cases (i : ZMod 4) : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by
  have hi : i.val < 4 := i.isLt; omega

theorem q8A_add_test (i j : ZMod 4) : q8A (i + j) = q8A i * q8A j := by
  rcases zmod4_cases i with rfl | rfl | rfl | rfl <;>
  rcases zmod4_cases j with rfl | rfl | rfl | rfl <;>
  ext r c <;> fin_cases r <;> fin_cases c <;>
  simp [q8A, M_i, Matrix.mul_apply, Fin.sum_univ_two, ZMod.val, ZMod.val_add, ZMod.val_natCast]
