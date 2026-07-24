import Mathlib
import InfoGeometry.Causal.CausalAlgebra

open Set Matrix

namespace InfoGeometry.Causal.ProofDAGRepresentation

open InfoGeometry.Causal.Algebra

/-!
# Proof DAG representation bridge

This file separates three layers that should not be identified by definition:

1. proof-theoretic causality as a DAG / partial order on declarations;
2. a local 2×2 Hodge-projector algebra (`O`, `d`, `δ`);
3. a representation structure connecting graph orientation to that algebra.

The audited slogan is:

* causality is graph antisymmetry / acyclicity;
* `d * δ = 0` and `δ * d = 0` certify that local past/future channels are
  algebraically disjoint;
* a representation theorem connects the graph layer to the operator layer.

This file does not identify graph acyclicity with `Δ_H = 0` by definition.

## BUCKET 1: CLOSED FINITE THEOREMS
- `forwardCone_self`
- `backwardCone_self`
- `cones_intersect_self`
- `O_sq`
- `d_idempotent`
- `δ_idempotent`
- `dδ_zero`
- `δd_zero`
- `represented_no_loop`
- `represented_edge_orthogonality`
- `represented_edge_orthogonality_rev`

## BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT WITNESSES
- `CausalRepresentation` is an explicit witness structure connecting a
  `ProofDAG` to the local projector algebra.

## BUCKET 3: OPEN CLOSURE DEBT
- This file does not prove `.olean` extraction correctness, InfoTree correctness,
  ArangoDB ingestion correctness, graph spectral completeness, or LeanTrail
  proposal soundness.
- The representation layer is deliberately narrow: it certifies orientation
  compatibility, not global semantic soundness of external tooling.
-/

/--
A proof dependency graph.

`a ≤ b` means declaration `a` is available as a dependency of declaration `b`.
This is proof-theoretic causality, not physical spacetime causality.
-/
structure ProofDAG (α : Type*) where
  le : α → α → Prop
  refl : ∀ a, le a a
  trans : ∀ {a b c}, le a b → le b c → le a c
  antisymm : ∀ {a b}, le a b → le b a → a = b

variable {α : Type*}

/-- Forward cone using a generic Preorder: all successors of `a`. -/
def forwardCone' [Preorder α] (a : α) : Set α := {b | a ≤ b}

/-- Backward cone using a generic Preorder: all predecessors of `a`. -/
def backwardCone' [Preorder α] (a : α) : Set α := {b | b ≤ a}

/-- Forward cone: all declarations reachable from `a`. -/
def forwardCone (G : ProofDAG α) (a : α) : Set α :=
  {b | G.le a b}

/-- Backward cone: all declarations that can reach `a`. -/
def backwardCone (G : ProofDAG α) (a : α) : Set α :=
  {b | G.le b a}

theorem forwardCone_self (G : ProofDAG α) (a : α) : a ∈ forwardCone G a :=
  G.refl a

theorem backwardCone_self (G : ProofDAG α) (a : α) : a ∈ backwardCone G a :=
  G.refl a

/--
If `b` is in both the forward and backward cone of `a`, then `b = a`.
Equivalently: nothing nontrivial is both downstream and upstream of `a`.
-/
theorem cones_intersect_self (G : ProofDAG α) (a b : α) :
    b ∈ forwardCone G a ∩ backwardCone G a → b = a := by
  rintro ⟨hab, hba⟩
  exact (G.antisymm hab hba).symm

/-- Local orientation operator — canonicalised in `CausalAlgebra.lean`. -/
abbrev O := InfoGeometry.Causal.Algebra.O

/-- Forward projector — canonicalised in `CausalAlgebra.lean`. -/
noncomputable abbrev d := InfoGeometry.Causal.Algebra.d

/-- Backward projector — canonicalised in `CausalAlgebra.lean`. -/
noncomputable abbrev δ := InfoGeometry.Causal.Algebra.δ

theorem O_sq : O * O = 1 := O_mul_O
theorem d_idempotent : d * d = d := d_sq_eq_d
theorem δ_idempotent : δ * δ = δ := δ_sq_eq_δ
theorem dδ_zero : d * δ = 0 := d_mul_δ_zero
theorem δd_zero : δ * d = 0 := δ_mul_d_zero

/--
A representation of proof-DAG orientation in the local projector algebra.

The forward/backward projector laws are stated only for nontrivial ordered pairs.
This avoids collapsing the reflexive relation `a ≤ a` into the contradictory
requirement that the diagonal edge be both `d` and `δ`.
-/
structure CausalRepresentation (G : ProofDAG α) where
  edgeOp : α → α → Matrix (Fin 2) (Fin 2) ℂ
  edgeOp_forward : ∀ {a b}, G.le a b → a ≠ b → edgeOp a b = d
  edgeOp_backward : ∀ {a b}, G.le b a → a ≠ b → edgeOp a b = δ
  no_two_way_nontrivial : ∀ {a b}, G.le a b → G.le b a → a = b

/--
The representation structure certifies the DAG-level no-loop statement.
-/
theorem represented_no_loop
    (G : ProofDAG α)
    (R : CausalRepresentation G)
    {a b : α}
    (hab : G.le a b)
    (hba : G.le b a) :
    a = b :=
  R.no_two_way_nontrivial hab hba

/--
For a nontrivial forward/backward represented pair, the local channels are
orthogonal: the forward-labelled edge composes with the backward-labelled edge
to zero.
-/
theorem represented_edge_orthogonality
    (G : ProofDAG α)
    (R : CausalRepresentation G)
    {a b : α}
    (hab : G.le a b)
    (hne : a ≠ b) :
    R.edgeOp a b * R.edgeOp b a = 0 := by
  rw [R.edgeOp_forward hab hne, R.edgeOp_backward (a := b) (b := a) hab hne.symm]
  exact dδ_zero

/--
The reverse-ordered local channel product also vanishes on a nontrivial
represented edge.
-/
theorem represented_edge_orthogonality_rev
    (G : ProofDAG α)
    (R : CausalRepresentation G)
    {a b : α}
    (hab : G.le a b)
    (hne : a ≠ b) :
    R.edgeOp b a * R.edgeOp a b = 0 := by
  rw [R.edgeOp_backward (a := b) (b := a) hab hne.symm, R.edgeOp_forward hab hne]
  exact δd_zero

end InfoGeometry.Causal.ProofDAGRepresentation
