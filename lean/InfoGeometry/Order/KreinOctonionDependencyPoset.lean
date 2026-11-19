/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Order.Interval.Finset.Basic
import Mathlib.Tactic.DeriveFintype
import Lean.Elab.Tactic.Omega

/-!
# The finite Krein--octonion dependency graph

This module formalizes the fifteen vertices and twenty-eight proposed dependency
edges. The order is the genuine reflexive transitive closure of those edges:
an explicit finite table is checked against its exact covering relation, and
mathlib's locally finite order theorem identifies its order with reachability.

The supplied levels strictly increase along paths, but they are not a rank
function for a graded poset. In fact, no natural-valued function can increase
by exactly one along every cover. The terminal pair has a least upper bound;
the thesis/shadow pair does not. These are statements about this particular
finite graph, not assertions of physical necessity, representation existence,
or uniqueness of a mathematical interpretation.
-/

namespace InfoGeometry.KreinOctonionDependencyPoset

/-- Names for the fifteen entries in the proposed dependency table. -/
inductive Node
  | cut | thesis | shadow | classical | projection | intrusion | unitarity
  | linearization | tension | obstruction | bridge | permanence
  | calibration | quantization | synthesis
  deriving DecidableEq, Fintype, Repr

open Node

/-- Exactly the predecessor sets specified in the input graph. -/
def predecessors : Node → Finset Node
  | .cut => ∅
  | .thesis => {.cut}
  | .shadow => {.cut}
  | .classical => {.thesis}
  | .projection => {.thesis, .shadow}
  | .intrusion => {.thesis, .shadow}
  | .unitarity => {.shadow}
  | .linearization => {.projection, .intrusion}
  | .tension => {.projection, .intrusion}
  | .obstruction => {.classical, .projection, .intrusion}
  | .bridge => {.classical, .linearization, .tension, .unitarity}
  | .permanence => {.obstruction, .tension, .unitarity}
  | .calibration => {.bridge, .permanence}
  | .quantization => {.bridge, .permanence}
  | .synthesis => {.calibration, .quantization}

/-- The supplied directed edges, before taking any transitive closure. -/
def edge (a b : Node) : Prop := a ∈ predecessors b

instance : DecidableRel edge := fun a b =>
  inferInstanceAs (Decidable (a ∈ predecessors b))

/-- A finite reachability table, including paths of length zero. Its exact
relationship with `edge` is proved below, rather than assumed. -/
private def upperTable : Node → Finset Node
  | .cut => Finset.univ
  | .thesis => {.thesis, .classical, .projection, .intrusion, .linearization,
      .tension, .obstruction, .bridge, .permanence, .calibration, .quantization, .synthesis}
  | .shadow => {.shadow, .projection, .intrusion, .unitarity, .linearization,
      .tension, .obstruction, .bridge, .permanence, .calibration, .quantization, .synthesis}
  | .classical => {.classical, .obstruction, .bridge, .permanence,
      .calibration, .quantization, .synthesis}
  | .projection => {.projection, .linearization, .tension, .obstruction,
      .bridge, .permanence, .calibration, .quantization, .synthesis}
  | .intrusion => {.intrusion, .linearization, .tension, .obstruction,
      .bridge, .permanence, .calibration, .quantization, .synthesis}
  | .unitarity => {.unitarity, .bridge, .permanence, .calibration, .quantization, .synthesis}
  | .linearization => {.linearization, .bridge, .calibration, .quantization, .synthesis}
  | .tension => {.tension, .bridge, .permanence, .calibration, .quantization, .synthesis}
  | .obstruction => {.obstruction, .permanence, .calibration, .quantization, .synthesis}
  | .bridge => {.bridge, .calibration, .quantization, .synthesis}
  | .permanence => {.permanence, .calibration, .quantization, .synthesis}
  | .calibration => {.calibration, .synthesis}
  | .quantization => {.quantization, .synthesis}
  | .synthesis => {.synthesis}

private def orderRel (a b : Node) : Prop := b ∈ upperTable a

private instance : DecidableRel orderRel := fun a b =>
  inferInstanceAs (Decidable (b ∈ upperTable a))

instance : PartialOrder Node where
  le := orderRel
  le_refl := by decide
  le_trans := by decide
  le_antisymm := by decide

instance : DecidableLE Node := fun a b => inferInstanceAs (Decidable (orderRel a b))

instance : DecidableLT Node := fun a b =>
  inferInstanceAs (Decidable (a ≤ b ∧ ¬ b ≤ a))

instance : LocallyFiniteOrder Node := Fintype.toLocallyFiniteOrder

instance : BoundedOrder Node where
  bot := .cut
  bot_le := by decide
  top := .synthesis
  le_top := by decide

theorem card_node : Fintype.card Node = 15 := by decide

/-- Every supplied edge is a cover and every cover is supplied: the graph
already is its transitive reduction. -/
theorem edge_iff_covBy : ∀ a b : Node, edge a b ↔ a ⋖ b := by
  unfold CovBy
  decide

theorem edge_eq_covBy : edge = (fun a b : Node => a ⋖ b) := by
  funext a b
  exact propext (edge_iff_covBy a b)

/-- The finite order table is precisely the reflexive transitive closure of
the original dependency edges. -/
theorem le_iff_reachable (a b : Node) :
    a ≤ b ↔ Relation.ReflTransGen edge a b := by
  rw [edge_eq_covBy]
  exact le_iff_reflTransGen_covBy

/-- Strict comparison means a nonempty directed path of supplied edges. -/
theorem reachable_iff_lt (a b : Node) :
    Relation.TransGen edge a b ↔ a < b := by
  rw [edge_eq_covBy]
  exact lt_iff_transGen_covBy.symm

/-- The supplied level labels. They provide a strict height, not a grading. -/
def level : Node → ℕ
  | .cut => 0
  | .thesis | .shadow => 1
  | .classical | .projection | .intrusion | .unitarity => 2
  | .linearization | .tension | .obstruction => 3
  | .bridge | .permanence => 4
  | .calibration | .quantization => 5
  | .synthesis => 6

theorem level_strictMono : StrictMono level := by decide

theorem level_lt_of_reachable {a b : Node} (h : Relation.TransGen edge a b) :
    level a < level b := level_strictMono ((reachable_iff_lt a b).mp h)

theorem reachable_irrefl (a : Node) : ¬ Relation.TransGen edge a a := by
  rw [reachable_iff_lt]
  exact lt_irrefl a

theorem reachable_asymm {a b : Node} (h : Relation.TransGen edge a b) :
    ¬ Relation.TransGen edge b a := by
  intro h'
  exact (level_lt_of_reachable h).not_gt (level_lt_of_reachable h')

/-- Each predecessor set is an antichain for the genuine dependency order. -/
theorem predecessors_incomparable : ∀ a b c : Node,
    a ∈ predecessors c → b ∈ predecessors c → a ≠ b → ¬ a ≤ b := by
  decide

theorem cut_reaches (a : Node) : Relation.ReflTransGen edge .cut a :=
  (le_iff_reachable .cut a).mp bot_le

theorem reaches_synthesis (a : Node) : Relation.ReflTransGen edge a .synthesis :=
  (le_iff_reachable a .synthesis).mp le_top

private theorem terminal_upper_bound : ∀ a : Node,
    calibration ≤ a → quantization ≤ a → a = synthesis := by decide

/-- The claimed terminal join exists in this particular poset. -/
theorem calibration_quantization_isLUB :
    IsLUB ({calibration, quantization} : Set Node) synthesis := by
  refine ⟨?_, ?_⟩
  · intro a _
    exact le_top
  · intro a ha
    have hc : calibration ≤ a := ha (by simp)
    have hq : quantization ≤ a := ha (by simp)
    exact le_of_eq (terminal_upper_bound a hc hq).symm

/-- The whole dependency poset is not a join semilattice. In particular,
thesis and shadow have the incomparable minimal upper bounds projection and intrusion. -/
theorem thesis_shadow_no_isLUB :
    ¬ ∃ a : Node, IsLUB ({thesis, shadow} : Set Node) a := by
  rintro ⟨a, ha⟩
  have ht : thesis ≤ a := ha.1 (by simp)
  have hs : shadow ≤ a := ha.1 (by simp)
  have hp : projection ∈ upperBounds ({thesis, shadow} : Set Node) := by
    change ∀ b : Node, b ∈ ({thesis, shadow} : Set Node) → b ≤ projection
    decide
  have hi : intrusion ∈ upperBounds ({thesis, shadow} : Set Node) := by
    change ∀ b : Node, b ∈ ({thesis, shadow} : Set Node) → b ≤ intrusion
    decide
  have impossible : ∀ b : Node,
      thesis ≤ b → shadow ≤ b → b ≤ projection → b ≤ intrusion → False := by decide
  exact impossible a ht hs (ha.2 hp) (ha.2 hi)

/-- A pair of two-edge and three-edge saturated paths from thesis to bridge
prevents every natural-valued cover rank, independently of the supplied labels. -/
theorem no_cover_rank :
    ¬ ∃ r : Node → ℕ, ∀ a b : Node, a ⋖ b → r b = r a + 1 := by
  rintro ⟨r, hr⟩
  have h₁ := hr thesis classical ((edge_iff_covBy _ _).mp (by decide))
  have h₂ := hr classical bridge ((edge_iff_covBy _ _).mp (by decide))
  have h₃ := hr thesis projection ((edge_iff_covBy _ _).mp (by decide))
  have h₄ := hr projection linearization ((edge_iff_covBy _ _).mp (by decide))
  have h₅ := hr linearization bridge ((edge_iff_covBy _ _).mp (by decide))
  omega

end InfoGeometry.KreinOctonionDependencyPoset
