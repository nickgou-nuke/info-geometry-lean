import InfoGeometry.Quantum.QuaternionSpinTimeReversal
import InfoGeometry.Algebra.FiniteSpinAlgebra

open InfoGeometry.Topology.Q8MonodromySpinorCover
open InfoGeometry.Quantum.QuaternionSpinTimeReversal

private theorem zmod4_cases (i : ZMod 4) : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by
  fin_cases i <;> simp

theorem q8A_add_test (i j : ZMod 4) : q8A (i + j) = q8A i * q8A j := by
  match i, j with
  | 0, 0 => change q8A 0 = q8A 0 * q8A 0; norm_num [q8A, ZMod.val]
  | 0, 1 => change q8A 1 = q8A 0 * q8A 1; norm_num [q8A, ZMod.val]
  | 0, 2 => change q8A 2 = q8A 0 * q8A 2; norm_num [q8A, ZMod.val]
  | 0, 3 => change q8A 3 = q8A 0 * q8A 3; norm_num [q8A, ZMod.val]
  | 1, 0 => change q8A 1 = q8A 1 * q8A 0; norm_num [q8A, ZMod.val]
  | 1, 1 => change q8A 2 = q8A 1 * q8A 1; norm_num [q8A, ZMod.val]
  | 1, 2 => change q8A 3 = q8A 1 * q8A 2; norm_num [q8A, ZMod.val]
  | 1, 3 => change q8A 0 = q8A 1 * q8A 3; norm_num [q8A, ZMod.val]
  | 2, 0 => change q8A 2 = q8A 2 * q8A 0; norm_num [q8A, ZMod.val]
  | 2, 1 => change q8A 3 = q8A 2 * q8A 1; norm_num [q8A, ZMod.val]
  | 2, 2 => change q8A 0 = q8A 2 * q8A 2; norm_num [q8A, ZMod.val]
  | 2, 3 => change q8A 1 = q8A 2 * q8A 3; norm_num [q8A, ZMod.val]
  | 3, 0 => change q8A 3 = q8A 3 * q8A 0; norm_num [q8A, ZMod.val]
  | 3, 1 => change q8A 0 = q8A 3 * q8A 1; norm_num [q8A, ZMod.val]
  | 3, 2 => change q8A 1 = q8A 3 * q8A 2; norm_num [q8A, ZMod.val]
  | 3, 3 => change q8A 2 = q8A 3 * q8A 3; norm_num [q8A, ZMod.val]
