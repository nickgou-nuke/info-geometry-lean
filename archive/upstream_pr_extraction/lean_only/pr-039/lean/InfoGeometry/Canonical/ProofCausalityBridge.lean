import InfoGeometry.Causal.CausalAlgebra
import DAG.GraphHodgeBridge

/-!
# InfoGeometry.Canonical.ProofCausalityBridge

Canonical bridge for the proof-causality / DAG-Hodge story.

This file does not add new algebra. It re-exports the existing owner
surfaces that matter for the causal reading of Lean developments:

* the abstract `CausalGraph` cones and acyclicity lemmas;
* the concrete 2x2 causal projector identities;
* the finite DAG Hodge bridge target.

Lean remains the proof authority. This module is a packaging surface.
-/

namespace InfoGeometry.Canonical.ProofCausalityBridge

open InfoGeometry.Causal.Algebra
open DAG

section CausalGraph

variable {α : Type*} [CausalGraph α]

/-- A node belongs to its own forward cone. -/
theorem forwardCone_self (a : α) :
    a ∈ CausalGraph.forwardCone a :=
  by simp [CausalGraph.forwardCone]

/-- A node belongs to its own backward cone. -/
theorem backwardCone_self (a : α) :
    a ∈ CausalGraph.backwardCone a :=
  by simp [CausalGraph.backwardCone]

/-- Forward cones are nonempty. -/
theorem forwardCone_nonempty (a : α) :
    (CausalGraph.forwardCone a).Nonempty :=
  CausalGraph.forwardCone_nonempty a

/-- Backward cones are nonempty. -/
theorem backwardCone_nonempty (a : α) :
    (CausalGraph.backwardCone a).Nonempty :=
  CausalGraph.backwardCone_nonempty a

/-- Acyclicity in graph form. -/
theorem acyclicity (a b : α) (hf : b ∈ CausalGraph.forwardCone a)
    (hb : b ∈ CausalGraph.backwardCone a) :
    a = b :=
  CausalGraph.acyclicity a b hf hb

/-- Forward cones are nested under the causal order. -/
theorem forwardCone_trans (a b : α) (h : b ∈ CausalGraph.forwardCone a) :
    CausalGraph.forwardCone b ⊆ CausalGraph.forwardCone a :=
  CausalGraph.forwardCone_trans a b h

/-- Backward cones are nested under the causal order. -/
theorem backwardCone_trans (a b : α) (h : b ∈ CausalGraph.backwardCone a) :
    CausalGraph.backwardCone b ⊆ CausalGraph.backwardCone a :=
  CausalGraph.backwardCone_trans a b h

/-- Forward and backward cones meet only at the node itself. -/
theorem cones_intersect_at_self (a : α) :
    CausalGraph.forwardCone a ∩ CausalGraph.backwardCone a = {a} :=
  CausalGraph.cones_intersect_at_self a

/-- Antisymmetry in cone form. -/
theorem cones_intersect_self_iff_antisymm (a : α) :
    CausalGraph.forwardCone a ∩ CausalGraph.backwardCone a = {a} :=
  CausalGraph.cones_intersect_at_self a

/-- No two-way causal loop except at the same declaration. -/
theorem acyclic_no_two_way_except_self (a b : α)
    (hf : b ∈ CausalGraph.forwardCone a)
    (hb : b ∈ CausalGraph.backwardCone a) :
    a = b :=
  CausalGraph.acyclicity a b hf hb

end CausalGraph

section ConcreteCausalAlgebra

/-!
The following identities are the operator analogue of the causal graph
facts above. They are not definitions of DAG acyclicity; they are the
chosen projector algebra on the 2×2 causal orientation space.
-/

/-- Concrete 2x2 forward projector identity. -/
theorem d_sq_eq_d : InfoGeometry.Causal.Algebra.d * InfoGeometry.Causal.Algebra.d =
    InfoGeometry.Causal.Algebra.d :=
  InfoGeometry.Causal.Algebra.d_sq_eq_d

/-- Concrete 2x2 backward projector identity. -/
theorem δ_sq_eq_δ : InfoGeometry.Causal.Algebra.δ * InfoGeometry.Causal.Algebra.δ =
    InfoGeometry.Causal.Algebra.δ :=
  InfoGeometry.Causal.Algebra.δ_sq_eq_δ

/-- Concrete 2x2 acyclicity identities. -/
theorem d_mul_δ_zero :
    InfoGeometry.Causal.Algebra.d * InfoGeometry.Causal.Algebra.δ = 0 :=
  InfoGeometry.Causal.Algebra.d_mul_δ_zero

/-- Concrete 2x2 acyclicity identities. -/
theorem δ_mul_d_zero :
    InfoGeometry.Causal.Algebra.δ * InfoGeometry.Causal.Algebra.d = 0 :=
  InfoGeometry.Causal.Algebra.δ_mul_d_zero

/-- Concrete Hodge Laplacian vanishes. -/
theorem Δ_H_zero :
    InfoGeometry.Causal.Algebra.Δ_H = 0 :=
  InfoGeometry.Causal.Algebra.Δ_H_zero

/-- Concrete completeness identity. -/
theorem d_add_δ_eq_one :
    InfoGeometry.Causal.Algebra.d + InfoGeometry.Causal.Algebra.δ = 1 :=
  InfoGeometry.Causal.Algebra.d_add_δ_eq_one

/-- Concrete causal involution recovery. -/
theorem d_sub_δ_eq_O :
    InfoGeometry.Causal.Algebra.d - InfoGeometry.Causal.Algebra.δ =
      InfoGeometry.Causal.Algebra.O :=
  InfoGeometry.Causal.Algebra.d_sub_δ_eq_O

/-- Concrete Dirac Laplacian identity. -/
theorem Δ_D_eq_one :
    InfoGeometry.Causal.Algebra.Δ_D = 1 :=
  InfoGeometry.Causal.Algebra.Δ_D_eq_one

/-- Orientation reversal of the causal involution. -/
theorem det_O :
    Matrix.det InfoGeometry.Causal.Algebra.O = -1 :=
  InfoGeometry.Causal.Algebra.det_O

/-- Balanced trace of the causal involution. -/
theorem tr_O :
    Matrix.trace InfoGeometry.Causal.Algebra.O = 0 :=
  InfoGeometry.Causal.Algebra.tr_O

end ConcreteCausalAlgebra

section DAGBridge

variable {α : Type*} [BEq α] [Hashable α]

/-- Canonical finite Hodge / Dirac / chiral bridge target for the declaration DAG. -/
theorem graphHodgeBridgeTarget :
    DAG.GraphHodgeBridgeTarget α :=
  DAG.graphHodgeBridgeTarget α

end DAGBridge

end InfoGeometry.Canonical.ProofCausalityBridge
