import InfoGeometry.Causal.ProofDAGRepresentation

/-!
# InfoGeometry.Canonical.ProofDAGRepresentationBridge

Canonical bridge for the finite proof-DAG representation layer.
-/

namespace InfoGeometry.Canonical.ProofDAGRepresentationBridge

open InfoGeometry.Causal.ProofDAGRepresentation

variable {α : Type*}

abbrev ProofDAG (α : Type*) := InfoGeometry.Causal.ProofDAGRepresentation.ProofDAG α
abbrev CausalRepresentation {α : Type*} (G : ProofDAG α) :=
  InfoGeometry.Causal.ProofDAGRepresentation.CausalRepresentation G

theorem forwardCone_self (G : ProofDAG α) (a : α) :
    a ∈ forwardCone G a :=
  InfoGeometry.Causal.ProofDAGRepresentation.forwardCone_self G a

theorem backwardCone_self (G : ProofDAG α) (a : α) :
    a ∈ backwardCone G a :=
  InfoGeometry.Causal.ProofDAGRepresentation.backwardCone_self G a

theorem cones_intersect_self (G : ProofDAG α) (a b : α) :
    b ∈ forwardCone G a ∩ backwardCone G a → b = a :=
  InfoGeometry.Causal.ProofDAGRepresentation.cones_intersect_self G a b

theorem represented_no_loop
    (G : ProofDAG α)
    (R : CausalRepresentation G)
    {a b : α}
    (hab : G.le a b)
    (hba : G.le b a) :
    a = b :=
  InfoGeometry.Causal.ProofDAGRepresentation.represented_no_loop G R hab hba

theorem represented_edge_orthogonality
    (G : ProofDAG α)
    (R : CausalRepresentation G)
    {a b : α}
    (hab : G.le a b)
    (hne : a ≠ b) :
    R.edgeOp a b * R.edgeOp b a = 0 :=
  InfoGeometry.Causal.ProofDAGRepresentation.represented_edge_orthogonality G R hab hne

theorem represented_edge_orthogonality_rev
    (G : ProofDAG α)
    (R : CausalRepresentation G)
    {a b : α}
    (hab : G.le a b)
    (hne : a ≠ b) :
    R.edgeOp b a * R.edgeOp a b = 0 :=
  InfoGeometry.Causal.ProofDAGRepresentation.represented_edge_orthogonality_rev G R hab hne

end InfoGeometry.Canonical.ProofDAGRepresentationBridge
