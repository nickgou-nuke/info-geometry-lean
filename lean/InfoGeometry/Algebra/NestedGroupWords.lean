/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.GroupTheory.FreeGroup.Basic

/-! # Labeled nested words and native free-group reduction

The node `node a l r` encodes an opening letter `a`, the nested word `l`,
the matching inverse letter, and then the word `r`. This is the native
binary-tree presentation of Dyck words with labels retained.

Reduction is proved before evaluation in any group, without a commutativity
assumption. Evaluation sends every such balanced word to the identity, so it
does not preserve enough information to reconstruct its parse tree.
-/

namespace InfoGeometry.Algebra.NestedGroupWords

variable {α : Type*}

/-- The labeled bracket traversal of a native binary tree. `true` opens and
`false` closes the matching bracket. -/
def bracketWord : BinaryTree α → List (α × Bool) :=
  BinaryTree.rec (motive := fun _ => List (α × Bool)) []
    (fun a _ _ wl wr => (a, true) :: (wl ++ (a, false) :: wr))

/-- Erasing labels gives exactly Mathlib's Dyck word of the underlying tree. -/
theorem bracketWord_erase (t : BinaryTree α) :
    (bracketWord t).map (fun s => cond s.2 DyckStep.U DyckStep.D) =
      (DyckWord.ofTree (t.map (fun _ => ()))).toList := by
  induction t with
  | nil => rfl
  | node a l r hl hr =>
    change
      ((a, true) :: (bracketWord l ++ (a, false) :: bracketWord r)).map
        (fun s => cond s.2 DyckStep.U DyckStep.D) = _
    simp only [List.map_cons, List.map_append, Bool.cond_true,
      Bool.cond_false, hl, hr, BinaryTree.map, DyckWord.ofTree]
    change _ =
      (([DyckStep.U] ++ (DyckWord.ofTree (l.map (fun _ => ()))).toList) ++ [DyckStep.D]) ++
        (DyckWord.ofTree (r.map (fun _ => ()))).toList
    simp only [List.cons_append, List.nil_append, List.append_assoc]

/-- Arbitrarily nested, correctly matched letters reduce to the empty word
using native free-group reductions, without choosing a target group. -/
theorem bracketWord_reduces (t : BinaryTree α) :
    FreeGroup.Red (bracketWord t) [] := by
  induction t with
  | nil => exact FreeGroup.Red.refl
  | node a l r hl hr =>
    have hinner : FreeGroup.Red
        ((a, true) :: (bracketWord l ++ (a, false) :: bracketWord r))
        ((a, true) :: (a, false) :: bracketWord r) :=
      FreeGroup.Red.cons_cons
        (FreeGroup.Red.append_append hl FreeGroup.Red.refl)
    exact hinner.trans ((FreeGroup.Red.Step.cons_not (b := true)).to_red.trans hr)

/-- The free-group quotient records the preceding reduction as equality. -/
theorem mk_bracketWord (t : BinaryTree α) :
    FreeGroup.mk (bracketWord t) = 1 := by
  change FreeGroup.mk (bracketWord t) = FreeGroup.mk []
  exact FreeGroup.Red.exact.mpr ⟨[], bracketWord_reduces t, FreeGroup.Red.refl⟩

/-- Every group-valued assignment evaluates a balanced labeled tree to one.
The group can be noncommutative, for example the units of an operator ring. -/
theorem bracketWord_prod {G : Type*} [Group G] (gate : α → G) (t : BinaryTree α) :
    ((bracketWord t).map (fun s => cond s.2 (gate s.1) (gate s.1)⁻¹)).prod = 1 := by
  rw [← FreeGroup.lift_mk, mk_bracketWord, map_one]

/-- A balanced subtree can be removed from an ordered context without
permuting either outer factor. -/
theorem bracketWord_context {G : Type*} [Group G] (gate : α → G)
    (t : BinaryTree α) (left right : G) :
    left * ((bracketWord t).map
      (fun s => cond s.2 (gate s.1) (gate s.1)⁻¹)).prod * right = left * right := by
  rw [bracketWord_prod, mul_one]

/-- Balanced-word evaluation cannot be an injective encoding of labeled
trees: a one-node tree and the empty tree already have the same value. -/
theorem bracketWord_prod_not_injective {G : Type*} [Group G] [Nonempty α]
    (gate : α → G) :
    ¬ Function.Injective (fun t : BinaryTree α =>
      ((bracketWord t).map (fun s => cond s.2 (gate s.1) (gate s.1)⁻¹)).prod) := by
  intro h
  obtain ⟨a⟩ := ‹Nonempty α›
  have heq :
      ((bracketWord (.node a .nil .nil)).map
        (fun s => cond s.2 (gate s.1) (gate s.1)⁻¹)).prod =
      ((bracketWord .nil).map
        (fun s => cond s.2 (gate s.1) (gate s.1)⁻¹)).prod := by
    rw [bracketWord_prod, bracketWord_prod]
  have htree := h heq
  cases htree

end InfoGeometry.Algebra.NestedGroupWords
