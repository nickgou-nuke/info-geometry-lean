/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import DAG.TwoComplex
import Mathlib.Tactic

/-!
# Self-loop incidence regression

The source-priority formula `if source then -1 else if target then 1` assigns `-1`
to a loop. The cellular incidence formula sums endpoint contributions, so the
source and target cancel. This file keeps a finite witness for that distinction.
-/
namespace DAG.SelfLoopIncidenceRegression

def oneLoop : TwoComplex Nat where
  base := {
    toGraph := {
      nodes := #[0]
      nodeToIdx := {}
      forward := #[#[(0, EdgeKind.type)]]
    }
    sccs := #[#[0]]
    sccOf := #[0]
    dag := #[#[]]
    preds := #[#[]]
    topo := #[0]
    idom := #[none]
    idomDepth := #[0]
  }
  edges := #[(0, 0)]
  faces := #[]
  digons := #[]

/-- The incorrect source-priority incidence rule, retained only as a regression comparison. -/
def sourcePriorityEntry (tc : TwoComplex Nat) : Matrix (Fin tc.edges.size)
    (Fin tc.base.toGraph.nodes.size) ℚ := fun i j =>
  let (u, v) := tc.edges[i.val]
  if j.val = u then -1 else if j.val = v then 1 else 0

/-- The old formula gave a nonzero boundary to a loop; the repaired owner matrix cancels it. -/
theorem old_priority_vs_canonical_loop_entry :
    sourcePriorityEntry oneLoop (⟨0, by decide⟩ : Fin oneLoop.edges.size)
      (⟨0, by decide⟩ : Fin oneLoop.base.toGraph.nodes.size) = (-1 : ℚ) ∧
    boundary1Matrix oneLoop (⟨0, by decide⟩ : Fin oneLoop.edges.size)
      (⟨0, by decide⟩ : Fin oneLoop.base.toGraph.nodes.size) = 0 := by
  constructor
  · norm_num [sourcePriorityEntry, oneLoop]
  · norm_num [boundary1Matrix, incidenceBoundaryCoeff, oneLoop]

/-- The executable array incidence matrix also has the canonical zero loop row. -/
theorem canonical_array_loop_entry :
    ((boundary1 oneLoop)[0]!)[0]! = 0 := by
  norm_num [boundary1, incidenceBoundaryCoeff, oneLoop]

end DAG.SelfLoopIncidenceRegression
