#!/usr/bin/env python3
import os
import subprocess
import sys

REPO_ROOT = "/home/goutev/info-geometry-lean"
if REPO_ROOT not in sys.path:
    sys.path.insert(0, REPO_ROOT)

from tools.build_lock import acquire_build_lock

SANDBOX_FILE = "/home/goutev/info-geometry-lean/.agents/sandbox_dominators_o1/lean/DAG/Dominators.lean"
TEST_FILE = "/home/goutev/info-geometry-lean/.agents/challenger_dominators_2/TestDominators.lean"

with open(SANDBOX_FILE, "r") as f:
    sandbox_code = f.read()

stress_theorems = """

-- ============================================================
-- ADVERSARIAL STRESS THEOREMS (CHALLENGER SUITE - DECIDE)
-- ============================================================

-- 1. Single Node DAG (N=1)
private def singleNodePreds : Array (Array Nat) := #[#[]]
private def singleNodeOrder : Array Nat := #[0]

theorem single_node_idom :
    buildIdom singleNodePreds (dominators singleNodePreds singleNodeOrder) = #[none] := by
  decide

theorem single_node_dominates :
    dominates (dominators singleNodePreds singleNodeOrder) 0 0 = true := by
  decide

theorem single_node_strict_dom :
    strictDominators (dominators singleNodePreds singleNodeOrder) 0 = #[] := by
  decide

-- 2. Disconnected 2-Node DAG (N=2, no edges)
private def disc2Preds : Array (Array Nat) := #[#[], #[]]
private def disc2Order : Array Nat := #[0, 1]

theorem disc2_idom :
    buildIdom disc2Preds (dominators disc2Preds disc2Order) = #[none, none] := by
  decide

theorem disc2_dominance :
    let dom := dominators disc2Preds disc2Order
    dominates dom 0 1 = false ∧
    dominates dom 1 0 = false ∧
    dominates dom 0 0 = true ∧
    dominates dom 1 1 = true := by
  decide

-- 3. Wide Diamond DAG (N=6: 0 -> 1,2,3,4 -> 5)
private def wideDiamondPreds : Array (Array Nat) :=
  #[#[], #[0], #[0], #[0], #[0], #[1, 2, 3, 4]]
private def wideDiamondOrder : Array Nat := #[0, 1, 2, 3, 4, 5]

theorem wide_diamond_idom :
    buildIdom wideDiamondPreds (dominators wideDiamondPreds wideDiamondOrder) =
      #[none, some 0, some 0, some 0, some 0, some 0] := by
  decide

-- 4. Byte Boundary Crossing (N=9: 0 -> 1 -> ... -> 8)
private def chain9Preds : Array (Array Nat) :=
  #[#[], #[0], #[1], #[2], #[3], #[4], #[5], #[6], #[7]]
private def chain9Order : Array Nat :=
  #[0, 1, 2, 3, 4, 5, 6, 7, 8]

theorem chain9_idom :
    buildIdom chain9Preds (dominators chain9Preds chain9Order) =
      #[none, some 0, some 1, some 2, some 3, some 4, some 5, some 6, some 7] := by
  decide

theorem chain9_dominates_boundary :
    let dom := dominators chain9Preds chain9Order
    dominates dom 0 8 = true ∧
    dominates dom 7 8 = true ∧
    dominates dom 8 8 = true ∧
    dominates dom 8 7 = false := by
  decide

-- 5. Disconnected Components with Internal Edges (0->1 and 2->3)
private def disconnCompPreds : Array (Array Nat) := #[#[], #[0], #[], #[2]]
private def disconnCompOrder : Array Nat := #[0, 2, 1, 3]

theorem disconn_comp_idom :
    buildIdom disconnCompPreds (dominators disconnCompPreds disconnCompOrder) =
      #[none, some 0, none, some 2] := by
  decide

theorem disconn_comp_cross_dominance :
    let dom := dominators disconnCompPreds disconnCompOrder
    dominates dom 0 2 = false ∧
    dominates dom 0 3 = false ∧
    dominates dom 2 0 = false ∧
    dominates dom 2 1 = false := by
  decide

-- 6. Empty / 0-Node DAG
theorem empty_dag_dominators :
    dominators #[] #[] = #[] := by
  decide

theorem empty_dag_idom :
    buildIdom #[] (dominators #[] #[]) = #[] := by
  decide

-- 7. Duplicate Predecessor Entries
private def dupPreds : Array (Array Nat) := #[#[], #[0, 0]]
private def dupOrder : Array Nat := #[0, 1]

theorem dup_preds_idom :
    buildIdom dupPreds (dominators dupPreds dupOrder) = #[none, some 0] := by
  decide

-- 8. Frontier and Lightcones (tested via native_decide because frontier/lightcone retain imperative loop)
theorem diamond_frontier_smoke_native :
    let dom := dominators diamondPreds diamondOrder
    dominatorFrontier diamondPreds dom 0 = #[] ∧
    dominatorFrontier diamondPreds dom 1 = #[3] ∧
    dominatorFrontier diamondPreds dom 2 = #[3] ∧
    dominatorFrontier diamondPreds dom 3 = #[] := by
  native_decide

theorem diamond_lightcone_smoke_native :
    let dom := dominators diamondPreds diamondOrder
    lightcone dom 0 = (#[1, 2, 3], #[]) ∧
    lightcone dom 3 = (#[], #[0]) := by
  native_decide

"""

target_marker = "end DAG.Dominators"
augmented_code = sandbox_code.replace(target_marker, stress_theorems + "\n" + target_marker)

with open(TEST_FILE, "w") as f:
    f.write(augmented_code)

print(f"Generated {TEST_FILE}.")

with acquire_build_lock(None, "challenger-dominators-lean-stress", block=True):
    res = subprocess.run(
        ["lake", "env", "lean", TEST_FILE],
        capture_output=True,
        text=True
    )
    print("Return code:", res.returncode)
    if res.stdout:
        print("STDOUT:\n", res.stdout)
    if res.stderr:
        print("STDERR:\n", res.stderr)

    if res.returncode != 0:
        print("LEAN STRESS TEST FAILED!")
        sys.exit(1)
    else:
        print("ALL LEAN ADVERSARIAL THEOREMS COMPILED AND VERIFIED CLEAN!")

