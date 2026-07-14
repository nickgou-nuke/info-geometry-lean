import InfoGeometry.Causal.ProofGraphExteriorCalculus
import InfoGeometry.Causal.ProofDAGRepresentation

/-!
# InfoGeometry.Canonical.ProofGraphExteriorCalculusBridge

Canonical bridge for the proof-graph exterior-calculus surface.

This file only re-exports the narrow owner lemmas from
`InfoGeometry.Causal.ProofGraphExteriorCalculus`. It does not claim a global
Hodge theorem for proof graphs.
-/

namespace ProofGraphExteriorCalculusBridge

open InfoGeometry.Causal.ProofGraphExteriorCalculus
open InfoGeometry.Causal.ProofDAGRepresentation

theorem grad_apply_of_edge
    {α : Type*} (G : DirectedProofGraph α) (f : ZeroForm α) {a b : α}
    (hab : G.edge a b) :
    grad G f a b = f b - f a :=
  InfoGeometry.Causal.ProofGraphExteriorCalculus.grad_apply_of_edge G f hab

theorem grad_apply_of_not_edge
    {α : Type*} (G : DirectedProofGraph α) (f : ZeroForm α) {a b : α}
    (hab : ¬ G.edge a b) :
    grad G f a b = 0 :=
  InfoGeometry.Causal.ProofGraphExteriorCalculus.grad_apply_of_not_edge G f hab

theorem grad_zero
    {α : Type*} (G : DirectedProofGraph α) :
    grad G (fun _ => (0 : ℝ)) = fun _ _ => 0 :=
  InfoGeometry.Causal.ProofGraphExteriorCalculus.grad_zero G

theorem grad_const
    {α : Type*} (G : DirectedProofGraph α) (c : ℝ) :
    grad G (fun _ => c) = fun _ _ => 0 :=
  InfoGeometry.Causal.ProofGraphExteriorCalculus.grad_const G c

theorem grad_ofProofDAG_apply
    {α : Type*} (G : ProofDAG α) (f : ZeroForm α) {a b : α}
    (hab : G.le a b) :
    grad (DirectedProofGraph.ofProofDAG G) f a b = f b - f a :=
  InfoGeometry.Causal.ProofGraphExteriorCalculus.grad_ofProofDAG_apply G f hab

end ProofGraphExteriorCalculusBridge
