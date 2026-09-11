import InfoGeometry.Causal.ProofDAGRepresentation
import InfoGeometry.Algebra.FiniteSpinAlgebra

namespace InfoGeometry.Causal.ProofGraphExteriorCalculus

open ProofDAGRepresentation

/-!
# Proof graph exterior-calculus surface

This file is a narrow owner-side first step toward discrete exterior calculus on
proof graphs. It does **not** formalize the full Hodge decomposition, graph curl,
Helmholtzian, global Laplacian equivalences, or any correctness claims about
`.olean` extraction, InfoTree serialization, or graph-database ingestion.

Instead, it only provides:

1. a directed proof-graph surface;
2. 0-forms and 1-forms on that surface;
3. a minimal discrete gradient on directed edges;
4. a small set of honest algebraic lemmas.

## BUCKET 1: CLOSED FINITE THEOREMS
- `grad_apply_of_edge`
- `grad_apply_of_not_edge`
- `grad_zero`
- `grad_const`
- `grad_ofProofDAG_apply`

## BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT WITNESSES
- `DirectedProofGraph.ofProofDAG` turns a `ProofDAG` reachability relation into a
  directed proof-graph surface.

## BUCKET 3: OPEN CLOSURE DEBT
- no graph curl
- no divergence
- no Laplacian / Helmholtzian
- no Hodge decomposition
- no proof that extracted Lean proof graphs satisfy any such global structure
-/

/--
A directed proof graph with edge relation `edge a b`, read as: there is a
primitive directed proof-step or dependency edge from `a` to `b`.
-/
structure DirectedProofGraph (α : Type*) where
  edge : α → α → Prop
  decEdge : DecidableRel edge

attribute [instance] DirectedProofGraph.decEdge

variable {α : Type*}

/-- Scalar potentials on proof states. -/
abbrev ZeroForm (α : Type*) := α → ℝ

/-- Directed edge flows on proof states. -/
abbrev OneForm (α : Type*) := α → α → ℝ

/--
The discrete gradient of a scalar potential, restricted to the directed edges of
`G`. Off-edge values are set to `0`.
-/
def grad (G : DirectedProofGraph α) (f : ZeroForm α) : OneForm α :=
  fun a b => if G.edge a b then f b - f a else 0

theorem grad_apply_of_edge
    (G : DirectedProofGraph α) (f : ZeroForm α) {a b : α}
    (hab : G.edge a b) :
    grad G f a b = f b - f a := by
  simp [grad, hab]

theorem grad_apply_of_not_edge
    (G : DirectedProofGraph α) (f : ZeroForm α) {a b : α}
    (hab : ¬ G.edge a b) :
    grad G f a b = 0 := by
  simp [grad, hab]

theorem grad_zero
    (G : DirectedProofGraph α) :
    grad G (fun _ => (0 : ℝ)) = fun _ _ => 0 := by
  funext a b
  by_cases hab : G.edge a b
  · simp [grad, hab]
  · simp [grad, hab]

theorem grad_const
    (G : DirectedProofGraph α) (c : ℝ) :
    grad G (fun _ => c) = fun _ _ => 0 := by
  funext a b
  by_cases hab : G.edge a b
  · simp [grad, hab]
  · simp [grad, hab]

/-- Forget only the reachability relation of a proof DAG as a directed graph. -/
noncomputable def DirectedProofGraph.ofProofDAG (G : ProofDAG α) : DirectedProofGraph α where
  edge := G.le
  decEdge := Classical.decRel _

theorem grad_ofProofDAG_apply
    (G : ProofDAG α) (f : ZeroForm α) {a b : α}
    (hab : G.le a b) :
    grad (DirectedProofGraph.ofProofDAG G) f a b = f b - f a := by
  exact grad_apply_of_edge _ _ hab

end InfoGeometry.Causal.ProofGraphExteriorCalculus
