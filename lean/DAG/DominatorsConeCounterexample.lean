/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import DAG.Dominators
import DAG.Algo.Traversal

/-! A dominator future is an unavoidable-path region, not all reachability. -/
namespace DAG.DominatorsConeCounterexample

private def diamondPreds : Array (Array Nat) := #[#[], #[0], #[0], #[1, 2]
]
private def diamondOrder : Array Nat := #[0, 1, 2, 3]
private def diamondAdj : DAG.Algo.Adj := #[#[1, 2], #[3], #[3], #[]]

/-- Node 3 is reachable from 1 along `1→3`, but 1 does not dominate 3 because
the alternate path `0→2→3` avoids it. -/
theorem reachability_is_larger_than_dominator_future :
    (DAG.Dominators.lightcone
        (DAG.Dominators.dominators diamondPreds diamondOrder) 1).1 = #[] ∧
      DAG.Algo.reachableFrom diamondAdj 1 = #[false, true, false, true] := by
  native_decide

end DAG.DominatorsConeCounterexample
