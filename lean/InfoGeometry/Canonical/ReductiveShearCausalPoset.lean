/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Data.Finset.Order
import Mathlib.Data.Fintype.Prod
import Mathlib.Order.Bounds.Basic
import Mathlib.Order.Interval.Finset.Basic
import Lean.Elab.Tactic.Omega

/-!
# The finite dependency poset of the reductive-frame/shear intake

This file formalizes the twelve labels and nineteen proposed covering edges
from the intake. The input graph is stipulated data: its reachability does
not prove the operator, geometric, psychological, or physical interpretations
of its labels. In particular there is no operation of subtraction or
idempotency defect on `Node`.

The order is native `PartialOrder`, constructed from the finite principal
ideals. Its strict part is proved to be exactly the transitive closure of
the input edges, and those edges are proved to be exactly `CovBy`.
The height supplied in the intake is strictly monotone, but this poset admits
no natural-number grading increasing by one on every cover. Several joins
fail to exist although the last node is the unique greatest element.
-/

namespace InfoGeometry.Canonical.ReductiveShearCausalPoset

/-- Labels from the input graph, without operator semantics. -/
inductive Node where
  | a0 | a1 | a2 | a3 | a4 | a5 | a6 | a7 | a8 | a9 | a10 | a11
  deriving DecidableEq, Repr

open Node

instance : Fintype Node where
  elems := {a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11}
  complete := by intro x; cases x <;> simp

/-- The proposed principal lower ideals, including each node itself. -/
def lowerIdeal : Node → Finset Node
  | a0 => {a0}
  | a1 => {a0, a1}
  | a2 => {a0, a2}
  | a3 => {a0, a1, a3}
  | a4 => {a0, a1, a2, a4}
  | a5 => {a0, a1, a2, a5}
  | a6 => {a0, a2, a6}
  | a7 => {a0, a1, a2, a3, a5, a6, a7}
  | a8 => {a0, a1, a2, a4, a5, a8}
  | a9 => {a0, a1, a2, a3, a4, a5, a8, a9}
  | a10 => {a0, a1, a2, a3, a4, a5, a6, a7, a10}
  | a11 => {a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11}

theorem lowerIdeal_injective : Function.Injective lowerIdeal := by
  intro a b h
  cases a <;> cases b <;> try rfl
  all_goals revert h; decide

instance : PartialOrder Node := PartialOrder.lift lowerIdeal lowerIdeal_injective

instance : DecidableLE Node :=
  fun a b => inferInstanceAs (Decidable (lowerIdeal a ⊆ lowerIdeal b))

instance : DecidableLT Node :=
  fun a b => inferInstanceAs (Decidable (a ≤ b ∧ ¬ b ≤ a))

instance : BoundedOrder Node where
  bot := a0
  top := a11
  bot_le := by intro x; cases x <;> decide
  le_top := by intro x; cases x <;> decide

instance : LocallyFiniteOrder Node := Fintype.toLocallyFiniteOrder

/-- The ideal table is exactly the lower-set table of the resulting order. -/
theorem le_iff_mem_lowerIdeal (a b : Node) : a ≤ b ↔ a ∈ lowerIdeal b := by
  cases a <;> cases b <;> decide

/-- All nineteen proposed edges, with no transitive edges silently added. -/
def coverEdges : Finset (Node × Node) :=
  {(a0, a1), (a0, a2), (a1, a3), (a1, a4), (a2, a4),
   (a1, a5), (a2, a5), (a2, a6), (a3, a7), (a5, a7),
   (a6, a7), (a4, a8), (a5, a8), (a3, a9), (a8, a9),
   (a4, a10), (a7, a10), (a9, a11), (a10, a11)}

/-- The input relation, prior to taking its transitive closure. -/
def Edge (a b : Node) : Prop := (a, b) ∈ coverEdges

instance : DecidableRel Edge := fun a b => inferInstanceAs (Decidable ((a, b) ∈ coverEdges))

theorem card_nodes : Fintype.card Node = 12 := by decide

theorem card_coverEdges : coverEdges.card = 19 := by decide

/-- Every proposed edge is minimal, and every order cover was proposed. -/
theorem edge_iff_covBy (a b : Node) : Edge a b ↔ a ⋖ b := by
  unfold CovBy
  cases a <;> cases b <;> decide

/-- The strict order is exactly the minimal transitive closure of the input. -/
theorem transGen_edge_iff_lt (a b : Node) :
    Relation.TransGen Edge a b ↔ a < b := by
  have he : Edge = (fun x y : Node => x ⋖ y) := by
    funext x y
    exact propext (edge_iff_covBy x y)
  rw [he]
  exact lt_iff_transGen_covBy.symm

/-- The full order is exactly the reflexive transitive closure of the input. -/
theorem reflTransGen_edge_iff_le (a b : Node) :
    Relation.ReflTransGen Edge a b ↔ a ≤ b := by
  have he : Edge = (fun x y : Node => x ⋖ y) := by
    funext x y
    exact propext (edge_iff_covBy x y)
  rw [he]
  exact le_iff_reflTransGen_covBy.symm

/-- There are 49 strict ordered pairs, hence 61 reflexive ordered pairs. -/
theorem card_strict_comparisons :
    (Finset.univ.filter fun ab : Node × Node => ab.1 < ab.2).card = 49 := by decide

theorem card_comparisons :
    (Finset.univ.filter fun ab : Node × Node => ab.1 ≤ ab.2).card = 61 := by decide

/-- The displayed height in the intake; it is not a cover-by-cover grading. -/
def height : Node → ℕ
  | a0 => 0
  | a1 | a2 => 1
  | a3 | a4 | a5 | a6 => 2
  | a7 | a8 => 3
  | a9 | a10 => 4
  | a11 => 5

theorem height_strictMono : StrictMono height := by decide

theorem height_le_five (a : Node) : height a ≤ 5 := by cases a <;> decide

theorem transGen_edge_height_lt {a b : Node} (h : Relation.TransGen Edge a b) :
    height a < height b := height_strictMono ((transGen_edge_iff_lt a b).1 h)

theorem transGen_edge_irrefl (a : Node) : ¬ Relation.TransGen Edge a a := by
  intro h
  exact Nat.lt_irrefl (height a) (transGen_edge_height_lt h)

theorem transGen_edge_asymm {a b : Node} (hab : Relation.TransGen Edge a b) :
    ¬ Relation.TransGen Edge b a := by
  intro hba
  exact Nat.lt_asymm (transGen_edge_height_lt hab) (transGen_edge_height_lt hba)

/-- Two saturated paths from `a1` to `a9` have different lengths.
Thus no assignment, including a replacement for `height`, increases by one
on every cover. -/
theorem no_cover_grading :
    ¬ ∃ r : Node → ℕ, ∀ a b : Node, a ⋖ b → r b = r a + 1 := by
  rintro ⟨r, hr⟩
  have h13 := hr a1 a3 ((edge_iff_covBy _ _).1 (by decide))
  have h39 := hr a3 a9 ((edge_iff_covBy _ _).1 (by decide))
  have h14 := hr a1 a4 ((edge_iff_covBy _ _).1 (by decide))
  have h48 := hr a4 a8 ((edge_iff_covBy _ _).1 (by decide))
  have h89 := hr a8 a9 ((edge_iff_covBy _ _).1 (by decide))
  omega

/-- The two primitive labels have no least upper bound in this order. -/
theorem no_lub_primitives : ¬ ∃ x : Node, IsLUB ({a1, a2} : Set Node) x := by
  simp only [IsLUB, IsLeast, upperBounds, lowerBounds, Set.mem_ofPred_eq]
  decide

/-- The opposite operations likewise have no join: `a8` and `a10` are
incomparable minimal upper bounds. A commutator label is not their supremum. -/
theorem no_lub_opposite_operations : ¬ ∃ x : Node, IsLUB ({a4, a5} : Set Node) x := by
  simp only [IsLUB, IsLeast, upperBounds, lowerBounds, Set.mem_ofPred_eq]
  decide

theorem primitive_labels_incomparable : ¬ a1 ≤ a2 ∧ ¬ a2 ≤ a1 := by decide

theorem opposite_operations_incomparable : ¬ a4 ≤ a5 ∧ ¬ a5 ≤ a4 := by decide

theorem final_branches_incomparable : ¬ a9 ≤ a10 ∧ ¬ a10 ≤ a9 := by decide

/-- The three stipulated predecessors of `a7` do have the asserted join. -/
theorem aporia_predecessors_isLUB : IsLUB ({a3, a5, a6} : Set Node) a7 := by
  simp only [IsLUB, IsLeast, upperBounds, lowerBounds, Set.mem_ofPred_eq]
  decide

/-- The bridge label is the join of its frame and commutator predecessors. -/
theorem bridge_predecessors_isLUB : IsLUB ({a3, a8} : Set Node) a9 := by
  simp only [IsLUB, IsLeast, upperBounds, lowerBounds, Set.mem_ofPred_eq]
  decide

/-- The tower label is a finite-order join, without constructing a limit. -/
theorem tower_predecessors_isLUB : IsLUB ({a4, a7} : Set Node) a10 := by
  simp only [IsLUB, IsLeast, upperBounds, lowerBounds, Set.mem_ofPred_eq]
  decide

/-- The final pair has a join, even though arbitrary joins do not exist. -/
theorem final_pair_isLUB : IsLUB ({a9, a10} : Set Node) a11 := by
  simp only [IsLUB, IsLeast, upperBounds, lowerBounds, Set.mem_ofPred_eq]
  decide

theorem greatest_iff_eq_a11 (x : Node) : (∀ y : Node, y ≤ x) ↔ x = a11 := by
  constructor
  · intro hx
    exact le_antisymm le_top (hx a11)
  · rintro rfl
    exact fun _ => le_top

/-- This is the precise order-theoretic exclusion available from `a3 < a7`.
It does not assert that an operator defect is nonzero. -/
theorem no_return_below_a3 {x : Node} (h : a7 ≤ x) : ¬ x ≤ a3 := by
  intro hx
  have hnot : ¬ a7 ≤ a3 := by decide
  exact hnot (h.trans hx)

/-- Every strictly ascending sequence would force unbounded natural heights,
which contradicts the height bound of five. -/
theorem no_infinite_strict_ascent (f : ℕ → Node) : ¬ ∀ n, f n < f (n + 1) := by
  intro hf
  have hn : ∀ n : ℕ, n ≤ height (f n) := by
    intro n
    induction n with
    | zero => exact Nat.zero_le _
    | succ n ih => exact Nat.succ_le_of_lt (lt_of_le_of_lt ih (height_strictMono (hf n)))
  have h6 := hn 6
  have hmax := height_le_five (f 6)
  omega

/-- A monotone sequence in this finite poset eventually stabilizes. The graph
cannot supply a theorem of endless strictly increasing prolongation. -/
theorem monotone_eventually_constant {f : ℕ → Node} (hf : Monotone f) :
    ∃ n : ℕ, ∀ m : ℕ, n ≤ m → f m = f n := by
  have hfin : (Set.range f).Finite := Set.toFinite _
  obtain ⟨x, ⟨n, rfl⟩, hmax⟩ := hfin.exists_maximal ⟨f 0, ⟨0, rfl⟩⟩
  refine ⟨n, ?_⟩
  intro m hnm
  exact le_antisymm (hmax ⟨m, rfl⟩ (hf hnm)) (hf hnm)

end InfoGeometry.Canonical.ReductiveShearCausalPoset
