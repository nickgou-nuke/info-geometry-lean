import Lean
import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import InfoGeometry.Canonical.SpectroscopicGauge

/-!
# Conductive Paths: Abstract Model and Compiler InfoTree Boundary

This module contains an abstract finite graph model and a compiler-facing path type.
Its defect values are explicit telemetry inputs; the file does not extract entropy,
lambda-reduction semantics, declaration dependencies, or ArangoDB data.

The abstract model defines nonnegative edge defects, additive path cost, and an
assigned exponential holonomy. Its compiler-facing path type records actual
`Lean.Elab.InfoTree` parent/child steps. Defects are explicit telemetry inputs;
they are not inferred from compiler syntax or proof semantics.

In the abstract model, zero defect defines conductivity and makes the assigned
exponential holonomy equal one. This does not establish entropy preservation or
homotopy invariance for compiler traces.
-/

namespace InfoGeometry.Canonical.InfoTreeGaugeHomotopy

open InfoGeometry.Canonical.SpectroscopicGauge
open Lean

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-- A node in the abstract directed-graph model. -/
structure InfoNode where
  id : ℕ
  name : String
  deriving DecidableEq, Repr

/-- An abstract directed edge with an externally supplied nonnegative defect. -/
structure InfoEdge (u v : InfoNode) where
  /-- The externally supplied edge defect. -/
  defect : ℝ
  defect_nonneg : 0 ≤ defect

/-- An abstract edge is conductive when its supplied defect is zero. -/
def InfoEdge.IsConductive {u v : InfoNode} (e : InfoEdge u v) : Prop :=
  e.defect = 0

/-! ### Compiler InfoTree Edge Boundary -/

/-- An immediate parent-to-child relation in Lean's elaborator information tree. -/
def InfoTree.HasImmediateChild : Lean.Elab.InfoTree → Lean.Elab.InfoTree → Prop
  | .context _ body, child => body = child
  | .node _ children, child => child ∈ children.toList
  | .hole _, _ => False

/-- A directed path composed of actual parent-to-child steps in a compiler InfoTree. -/
inductive CompilerInfoPath : Lean.Elab.InfoTree → Lean.Elab.InfoTree → Type where
  | nil (tree : Lean.Elab.InfoTree) : CompilerInfoPath tree tree
  | cons {parent child target : Lean.Elab.InfoTree}
      (step : InfoTree.HasImmediateChild parent child)
      (rest : CompilerInfoPath child target) : CompilerInfoPath parent target

/-- Concatenate compiler InfoTree paths at their shared endpoint. -/
def CompilerInfoPath.append : {a b c : Lean.Elab.InfoTree} →
    CompilerInfoPath a b → CompilerInfoPath b c → CompilerInfoPath a c
  | _, _, _, .nil _, second => second
  | _, _, _, .cons step rest, second => .cons step (rest.append second)

/-- A compiler InfoTree path with explicit nonnegative telemetry defect.

The path witness is compiler data. The numeric defect is supplied by telemetry;
Lean's InfoTree does not define an entropy metric. -/
structure CompilerInfoEdge (parent child : Lean.Elab.InfoTree) where
  followsInfoTree : CompilerInfoPath parent child
  defect : ℝ
  defect_nonneg : 0 ≤ defect

/-- Conductivity means the supplied defect attached to an InfoTree path is zero. -/
def CompilerInfoEdge.IsConductive {parent child : Lean.Elab.InfoTree}
    (e : CompilerInfoEdge parent child) : Prop := e.defect = 0

@[simp]
theorem CompilerInfoEdge.conductive_iff_zero {parent child : Lean.Elab.InfoTree}
    (e : CompilerInfoEdge parent child) : e.IsConductive ↔ e.defect = 0 := Iff.rfl

/-- Compose compiler paths and add their telemetry defects. -/
def CompilerInfoEdge.comp {parent middle target : Lean.Elab.InfoTree}
    (e₁ : CompilerInfoEdge parent middle) (e₂ : CompilerInfoEdge middle target) :
    CompilerInfoEdge parent target where
  followsInfoTree := CompilerInfoPath.append e₁.followsInfoTree e₂.followsInfoTree
  defect := e₁.defect + e₂.defect
  defect_nonneg := add_nonneg e₁.defect_nonneg e₂.defect_nonneg

@[simp]
theorem CompilerInfoEdge.comp_defect {parent middle target : Lean.Elab.InfoTree}
    (e₁ : CompilerInfoEdge parent middle) (e₂ : CompilerInfoEdge middle target) :
    (CompilerInfoEdge.comp e₁ e₂).defect = e₁.defect + e₂.defect := rfl

/-- Composition preserves zero-defect conductivity for compiler-derived paths. -/
theorem CompilerInfoEdge.conductive_comp {parent middle target : Lean.Elab.InfoTree}
    (e₁ : CompilerInfoEdge parent middle) (e₂ : CompilerInfoEdge middle target)
    (h₁ : e₁.IsConductive) (h₂ : e₂.IsConductive) :
    (CompilerInfoEdge.comp e₁ e₂).IsConductive := by
  unfold CompilerInfoEdge.IsConductive at *
  simp [h₁, h₂]

/-- Composition in the abstract model; every composable pair has a composite edge. -/
def InfoEdge.comp {u v w : InfoNode} (e1 : InfoEdge u v) (e2 : InfoEdge v w) : InfoEdge u w where
  defect := e1.defect + e2.defect
  defect_nonneg := add_nonneg e1.defect_nonneg e2.defect_nonneg

@[simp]
theorem InfoEdge.comp_defect {u v w : InfoNode} (e1 : InfoEdge u v) (e2 : InfoEdge v w) :
    (InfoEdge.comp e1 e2).defect = e1.defect + e2.defect := rfl

/-- Composition of conductive edges is conductive (Conductance Conservation). -/
theorem conductive_comp {u v w : InfoNode}
    (e1 : InfoEdge u v) (e2 : InfoEdge v w)
    (h1 : e1.IsConductive) (h2 : e2.IsConductive) :
    (InfoEdge.comp e1 e2).IsConductive := by
  unfold InfoEdge.IsConductive at *
  simp [h1, h2]

/-- A finite directed path in the abstract model. -/
inductive InfoPath : InfoNode → InfoNode → Type where
  | nil (u : InfoNode) : InfoPath u u
  | cons {u v w : InfoNode} (e : InfoEdge u v) (p : InfoPath v w) : InfoPath u w

/-- Total accumulated supplied defect along an abstract path. -/
def InfoPath.totalDefect : {u v : InfoNode} → InfoPath u v → ℝ
  | _, _, .nil _ => 0
  | _, _, .cons e rest => e.defect + rest.totalDefect

/-- Every path has non-negative total information defect. -/
theorem InfoPath.totalDefect_nonneg {u v : InfoNode} (p : InfoPath u v) :
    0 ≤ p.totalDefect := by
  induction p with
  | nil => simp [totalDefect]
  | cons e rest ih =>
      simp only [totalDefect]
      exact add_nonneg e.defect_nonneg ih

/-- An abstract path is conductive when its total supplied defect is zero. -/
def InfoPath.IsConductive {u v : InfoNode} (p : InfoPath u v) : Prop :=
  p.totalDefect = 0

/-- Concatenation of two abstract paths. -/
def InfoPath.append : {u v w : InfoNode} → InfoPath u v → InfoPath v w → InfoPath u w
  | _, _, _, .nil _, p2 => p2
  | _, _, _, .cons e rest, p2 => .cons e (rest.append p2)

@[simp]
theorem InfoPath.totalDefect_append {u v w : InfoNode}
    (p1 : InfoPath u v) (p2 : InfoPath v w) :
    (p1.append p2).totalDefect = p1.totalDefect + p2.totalDefect := by
  induction p1 with
  | nil => simp [append, totalDefect]
  | cons e rest ih =>
      simp [append, totalDefect, ih, add_assoc]

/-- Concatenation of conductive paths is conductive. -/
theorem conductive_append {u v w : InfoNode}
    (p1 : InfoPath u v) (p2 : InfoPath v w)
    (h1 : p1.IsConductive) (h2 : p2.IsConductive) :
    (p1.append p2).IsConductive := by
  unfold InfoPath.IsConductive at *
  simp [h1, h2]

/-- **The Shunting Theorem (Node Contraction along Conductive Paths)**:
If $u \to w \to v$ is a conductive two-step path where $w$ does not add new information,
it can be shunted into a single composite edge $u \to v$ whose conductance is conserved. -/
theorem conductive_node_shunting {u v w : InfoNode}
    (e1 : InfoEdge u v) (e2 : InfoEdge v w)
    (h1 : e1.IsConductive) (h2 : e2.IsConductive) :
    ∃ (e_shunted : InfoEdge u w), e_shunted.IsConductive ∧
      e_shunted.defect = e1.defect + e2.defect := by
  refine ⟨InfoEdge.comp e1 e2, conductive_comp e1 e2 h1 h2, rfl⟩

/-- Exponential holonomy assigned to an abstract path from its total defect. -/
noncomputable def InfoPath.holonomy {u v : InfoNode} (p : InfoPath u v) : ℝ :=
  Real.exp (-p.totalDefect)

/-- Holonomy is multiplicative under concatenation because the supplied path
defect is additive. This is an algebraic score in the abstract path model. -/
theorem InfoPath.holonomy_append {u v w : InfoNode}
    (p₁ : InfoPath u v) (p₂ : InfoPath v w) :
    (p₁.append p₂).holonomy = p₁.holonomy * p₂.holonomy := by
  change Real.exp (-((p₁.append p₂).totalDefect)) =
    Real.exp (-p₁.totalDefect) * Real.exp (-p₂.totalDefect)
  rw [InfoPath.totalDefect_append, neg_add, Real.exp_add]

/-- A conductive path has unit holonomy ($\operatorname{Hol} = 1$). -/
theorem conductive_holonomy_eq_one {u v : InfoNode} (p : InfoPath u v)
    (hcond : p.IsConductive) : p.holonomy = 1 := by
  unfold InfoPath.holonomy InfoPath.IsConductive at *
  rw [hcond, neg_zero, Real.exp_zero]

/-- The assigned holonomy is strictly positive along any abstract path. -/
theorem InfoPath.holonomy_pos {u v : InfoNode} (p : InfoPath u v) :
    0 < p.holonomy :=
  Real.exp_pos _

/-- Assigned holonomy is at most one for paths with nonnegative supplied defect. -/
theorem InfoPath.holonomy_le_one {u v : InfoNode} (p : InfoPath u v) :
    p.holonomy ≤ 1 := by
  unfold holonomy
  have hpos := p.totalDefect_nonneg
  have hneg : -p.totalDefect ≤ 0 := by linarith
  have h_exp := Real.exp_le_exp_of_le hneg
  rw [Real.exp_zero] at h_exp
  exact h_exp

/-- A closed abstract path with zero defect has unit assigned holonomy. -/
theorem conductive_loop_curvature_vanishing {u : InfoNode} (loop : InfoPath u u)
    (hcond : loop.IsConductive) :
    loop.holonomy = 1 ∧ loop.totalDefect = 0 :=
  ⟨conductive_holonomy_eq_one loop hcond, hcond⟩

/-- Conductive reachability in the abstract graph model. -/
def IsConductivelyReachable (seed capstone : InfoNode) : Prop :=
  ∃ p : InfoPath seed capstone, p.IsConductive

/-- Conductive reachability is transitive under path concatenation. -/
theorem conductive_reachability_trans (u v w : InfoNode)
    (huv : IsConductivelyReachable u v) (hvw : IsConductivelyReachable v w) :
    IsConductivelyReachable u w := by
  rcases huv with ⟨p1, hp1⟩
  rcases hvw with ⟨p2, hp2⟩
  exact ⟨p1.append p2, conductive_append p1 p2 hp1 hp2⟩

/-- Concatenating conductive path witnesses preserves abstract reachability. -/
theorem shunting_preserves_reachability (seed intermediate capstone : InfoNode)
    (h1 : IsConductivelyReachable seed intermediate)
    (h2 : IsConductivelyReachable intermediate capstone) :
    IsConductivelyReachable seed capstone :=
  conductive_reachability_trans seed intermediate capstone h1 h2

end InfoGeometry.Canonical.InfoTreeGaugeHomotopy
