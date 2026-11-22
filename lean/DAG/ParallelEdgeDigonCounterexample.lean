/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import DAG.SelfLoopIncidenceRegression
import Mathlib.Tactic

/-! Endpoint-only reciprocal-edge pairing conflates parallel edges of
different kinds. The alternative same-kind policy is explicit in the witness. -/
namespace DAG.ParallelEdgeDigonCounterexample

open DAG.SelfLoopIncidenceRegression

def parallelMixedGraph : DAG.HydratedGraph Nat :=
  { oneLoop.base with
    toGraph := { oneLoop.base.toGraph with
      nodes := #[0, 1]
      forward := #[#[(1, DAG.EdgeKind.type), (1, DAG.EdgeKind.value)],
                   #[(0, DAG.EdgeKind.type)]] } }

def endpointPolicyComplex : DAG.TwoComplex Nat :=
  DAG.buildTwoComplex parallelMixedGraph

/-- Same-kind-only policy keeps the first type edge paired with its reverse. -/
def sameKindPolicyComplex : DAG.TwoComplex Nat :=
  { endpointPolicyComplex with digons := #[(0, 2)] }

/-- A triangle with two parallel direct edges, one for each dependency kind. -/
def parallelShortcutGraph : DAG.HydratedGraph Nat :=
  { oneLoop.base with
    toGraph := { oneLoop.base.toGraph with
      nodes := #[0, 1, 2]
      forward := #[#[(1, DAG.EdgeKind.type), (2, DAG.EdgeKind.type),
                     (2, DAG.EdgeKind.value)],
                   #[(2, DAG.EdgeKind.type)], #[]] } }

def parallelShortcutComplex : DAG.TwoComplex Nat :=
  DAG.buildTwoComplex parallelShortcutGraph

/-- A triangle with parallel middle-path edges of different dependency kinds. -/
def parallelPathGraph : DAG.HydratedGraph Nat :=
  { oneLoop.base with
    toGraph := { oneLoop.base.toGraph with
      nodes := #[0, 1, 2]
      forward := #[#[(1, DAG.EdgeKind.type), (2, DAG.EdgeKind.type)],
                   #[(2, DAG.EdgeKind.type), (2, DAG.EdgeKind.value)], #[]] } }

def parallelPathComplex : DAG.TwoComplex Nat :=
  DAG.buildTwoComplex parallelPathGraph

/-- The builder matches reciprocal edges one-to-one and only within the same
edge kind, leaving the unmatched parallel value edge unfilled. -/
theorem builder_pairs_parallel_edges_one_to_one :
    endpointPolicyComplex.edges = #[(0, 1), (0, 1), (1, 0)] ∧
      endpointPolicyComplex.digons = #[(0, 2)] ∧
      DAG.boundarySquaredZero endpointPolicyComplex = true ∧
      DAG.betti1 endpointPolicyComplex = 1 := by
  native_decide

/-- The explicit same-kind complex agrees with the canonical builder result. -/
theorem same_kind_policy_agrees_with_builder :
    sameKindPolicyComplex.digons = endpointPolicyComplex.digons ∧
      DAG.betti1 sameKindPolicyComplex = 1 ∧
      DAG.boundarySquaredZero sameKindPolicyComplex = true := by
  native_decide

/-- Parallel shortcut edges produce separate face cells. The old single-index
endpoint map silently discarded one of them. -/
theorem builder_preserves_parallel_shortcut_faces :
    parallelShortcutComplex.edges =
        #[(0, 1), (0, 2), (0, 2), (1, 2)] ∧
      parallelShortcutComplex.faces = #[(0, 3, 1), (0, 3, 2)] ∧
      DAG.boundarySquaredZero parallelShortcutComplex = true ∧
      DAG.betti1 parallelShortcutComplex = 0 := by
  native_decide

/-- Each parallel occurrence in the two-edge path also yields its own face. -/
theorem builder_preserves_parallel_path_faces :
    parallelPathComplex.edges =
        #[(0, 1), (0, 2), (1, 2), (1, 2)] ∧
      parallelPathComplex.faces = #[(0, 2, 1), (0, 3, 1)] ∧
      DAG.boundarySquaredZero parallelPathComplex = true ∧
      DAG.betti1 parallelPathComplex = 0 := by
  native_decide

end DAG.ParallelEdgeDigonCounterexample
