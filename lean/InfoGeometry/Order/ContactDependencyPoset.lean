/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Logic.Relation
import Mathlib.Order.Cover
import Mathlib.Order.Bounds.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Lean.Elab.Tactic.Omega

/-!
# The supplied fifteen-node dependency diagram

This file checks the combinatorics of the diagram supplied in the contact
grading intake. Labels name vertices; they do not assert implications between
the philosophical or geometric claims attached to those vertices.

The listed edges are exactly the covers of a bounded partial order. The
displayed level function is a strict height, but no function increases by one
on every cover. The order is not a lattice, although the specified final pair
has the stated least upper bound.
-/

namespace InfoGeometry.Order.ContactDependencyPoset

/-- The fifteen labels of the supplied diagram. -/
inductive Node
  | cut | thesis | shadow | internal | projection | intrusion | ground
  | gravity | tension | defect | contact | obstruction | holonomy | bianchi | synthesis
  deriving DecidableEq

open Node

instance : Fintype Node where
  elems := {cut, thesis, shadow, internal, projection, intrusion, ground,
    gravity, tension, defect, contact, obstruction, holonomy, bianchi, synthesis}
  complete v := by cases v <;> decide

/-- Exactly the predecessor sets in the supplied diagram. -/
def predecessors : Node → Finset Node
  | cut => ∅
  | thesis | shadow => {cut}
  | internal => {thesis}
  | projection | intrusion => {thesis, shadow}
  | ground => {shadow}
  | gravity | tension => {projection, intrusion}
  | defect => {internal, projection, intrusion}
  | contact => {internal, gravity, tension, ground}
  | obstruction => {defect, tension, ground}
  | holonomy | bianchi => {contact, obstruction}
  | synthesis => {holonomy, bianchi}

/-- An edge of the input diagram, with its original orientation. -/
def Edge (a b : Node) : Prop := a ∈ predecessors b

instance : DecidableRel Edge := fun _ _ => inferInstanceAs (Decidable (_ ∈ _))

/-- The reflexive ancestor table. Its agreement with edge reachability is
proved below; the table gives computable order comparisons. -/
def ancestors : Node → Finset Node
  | cut => {cut}
  | thesis => {cut, thesis}
  | shadow => {cut, shadow}
  | internal => {cut, thesis, internal}
  | projection => {cut, thesis, shadow, projection}
  | intrusion => {cut, thesis, shadow, intrusion}
  | ground => {cut, shadow, ground}
  | gravity => {cut, thesis, shadow, projection, intrusion, gravity}
  | tension => {cut, thesis, shadow, projection, intrusion, tension}
  | defect => {cut, thesis, shadow, internal, projection, intrusion, defect}
  | contact => {cut, thesis, shadow, internal, projection, intrusion, ground,
      gravity, tension, contact}
  | obstruction => {cut, thesis, shadow, internal, projection, intrusion,
      ground, tension, defect, obstruction}
  | holonomy => {cut, thesis, shadow, internal, projection, intrusion, ground,
      gravity, tension, defect, contact, obstruction, holonomy}
  | bianchi => {cut, thesis, shadow, internal, projection, intrusion, ground,
      gravity, tension, defect, contact, obstruction, bianchi}
  | synthesis => Finset.univ

set_option maxRecDepth 4096 in
instance : PartialOrder Node where
  le a b := a ∈ ancestors b
  le_refl := by decide
  le_trans := by decide
  le_antisymm := by decide

instance : DecidableLE Node := fun a b => inferInstanceAs (Decidable (a ∈ ancestors b))
instance : DecidableLT Node := fun a b => inferInstanceAs (Decidable (a ≤ b ∧ ¬ b ≤ a))

/-- The levels printed in the intake, interpreted as a height function. -/
def height : Node → ℕ
  | cut => 0
  | thesis | shadow => 1
  | internal | projection | intrusion | ground => 2
  | gravity | tension | defect => 3
  | contact | obstruction => 4
  | holonomy | bianchi => 5
  | synthesis => 6

theorem card_node : Fintype.card Node = 15 := by decide

theorem card_edges : (Finset.univ.sum fun b : Node => (predecessors b).card) = 28 := by
  decide

set_option maxRecDepth 4096 in
theorem height_strictMono : StrictMono height := by decide

set_option maxRecDepth 4096 in
theorem edge_iff_covBy : ∀ a b : Node, Edge a b ↔ a ⋖ b := by
  unfold CovBy
  decide

theorem edge_height_lt {a b : Node} (h : Edge a b) : height a < height b :=
  height_strictMono ((edge_iff_covBy a b).mp h).1

theorem edge_transGen_height_lt {a b : Node} (h : Relation.TransGen Edge a b) :
    height a < height b := by
  induction h with
  | single h => exact edge_height_lt h
  | tail _ h ih => exact lt_trans ih (edge_height_lt h)

/-- There is no nonempty directed cycle in the supplied graph. -/
theorem edge_transGen_irrefl (a : Node) : ¬ Relation.TransGen Edge a a := by
  intro h
  exact (Nat.lt_irrefl _) (edge_transGen_height_lt h)

private theorem predecessor_step :
    ∀ a b : Node, a < b → ∃ p : Node, a ≤ p ∧ Edge p b := by decide

/-- The computed partial order is exactly reflexive transitive edge reachability. -/
theorem le_iff_reflTransGen (a b : Node) :
    a ≤ b ↔ Relation.ReflTransGen Edge a b := by
  constructor
  · intro hab
    generalize hn : height b = n
    induction n using Nat.strong_induction_on generalizing a b with
    | h n ih =>
      by_cases heq : a = b
      · subst a
        exact Relation.ReflTransGen.refl
      · obtain ⟨p, hap, hpb⟩ := predecessor_step a b (lt_of_le_of_ne hab heq)
        have hp : height p < n := by rw [← hn]; exact edge_height_lt hpb
        exact Relation.ReflTransGen.tail (ih (height p) hp a p hap rfl) hpb
  · intro h
    induction h with
    | refl => exact le_rfl
    | tail _ h ih => exact le_trans ih ((edge_iff_covBy _ _).mp h).1.le

instance : OrderBot Node where
  bot := cut
  bot_le := by decide

instance : OrderTop Node where
  top := synthesis
  le_top := by decide

/-- Each listed predecessor set is an antichain in the resulting order. -/
theorem predecessors_incomparable :
    ∀ a b v : Node, Edge a v → Edge b v → a ≤ b → a = b := by decide

/-- The particular terminal pair has a least upper bound. -/
theorem terminal_isLUB : IsLUB ({holonomy, bianchi} : Set Node) synthesis := by
  unfold IsLUB IsLeast upperBounds lowerBounds
  decide

/-- The input diagram has no join for the thesis/shadow pair. -/
theorem thesis_shadow_no_isLUB :
    ¬ ∃ v : Node, IsLUB ({thesis, shadow} : Set Node) v := by
  unfold IsLUB IsLeast upperBounds lowerBounds
  decide

/-- No alternative numerical rank can increase by one along every cover.
The two paths `thesis → internal → contact` and
`thesis → projection → gravity → contact` already contradict this. -/
theorem no_cover_rank :
    ¬ ∃ r : Node → ℕ, ∀ a b : Node, a ⋖ b → r b = r a + 1 := by
  rintro ⟨r, hr⟩
  have hti := hr thesis internal ((edge_iff_covBy _ _).mp (by decide))
  have hic := hr internal contact ((edge_iff_covBy _ _).mp (by decide))
  have htp := hr thesis projection ((edge_iff_covBy _ _).mp (by decide))
  have hpg := hr projection gravity ((edge_iff_covBy _ _).mp (by decide))
  have hgc := hr gravity contact ((edge_iff_covBy _ _).mp (by decide))
  omega

end InfoGeometry.Order.ContactDependencyPoset
