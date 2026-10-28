/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.MatrixPeirceZorn.MatrixReassociation
import Mathlib.Order.Defs.PartialOrder
import Lean.Elab.Tactic.Omega

/-!
# The partial order of oriented reassociation

Right rotations preserve the ordered word of arbitrary matrix-valued leaves.
Their reachability relation is antisymmetric: the sum of the lengths of left
subtrees strictly decreases at each rotation. `rotationOrder` packages this
relation as a native `PartialOrder` without installing a global order instance.
-/

namespace InfoGeometry.Canonical.MatrixPeirceZorn.Zorn.Reassociation

variable {n : Type*}

/-- The sum, over all internal vertices, of the number of leaves to the left. -/
def weight : Term n → ℕ
  | .of _ => 0
  | .mul s t => weight s + weight t + s.length

@[simp] theorem weight_of (X : Carrier n) : weight (.of X) = 0 := rfl

@[simp] theorem weight_mul (s t : Term n) :
    weight (s * t) = weight s + weight t + s.length := rfl

namespace Context

theorem plug_length_eq (C : Context n) {s t : Term n} (h : s.length = t.length) :
    (C.plug s).length = (C.plug t).length := by
  induction C with
  | hole => exact h
  | left C u ih =>
      simpa only [plug, FreeMagma.length] using congrArg (fun k => k + u.length) ih
  | right u C ih =>
      simpa only [plug, FreeMagma.length] using congrArg (fun k => u.length + k) ih

theorem plug_weight_lt (C : Context n) {s t : Term n}
    (hl : s.length = t.length) (hw : weight s < weight t) :
    weight (C.plug s) < weight (C.plug t) := by
  induction C with
  | hole => exact hw
  | left C u ih =>
      have hlen := C.plug_length_eq hl
      simp only [plug, weight_mul]
      omega
  | right u C ih =>
      simp only [plug, weight_mul]
      omega

theorem plug_word_eq (C : Context n) {s t : Term n}
    (h : FreeMagma.toFreeSemigroup s = FreeMagma.toFreeSemigroup t) :
    FreeMagma.toFreeSemigroup (C.plug s) =
      FreeMagma.toFreeSemigroup (C.plug t) := by
  induction C with
  | hole => exact h
  | left C u ih => simp only [plug, map_mul, ih]
  | right u C ih => simp only [plug, map_mul, ih]

end Context

namespace Rotation

theorem length_eq (r : Rotation n) : r.source.length = r.target.length := by
  apply r.context.plug_length_eq
  simp only [FreeMagma.length, Nat.add_assoc]

theorem weight_lt (r : Rotation n) : weight r.target < weight r.source := by
  apply r.context.plug_weight_lt
  · simp only [FreeMagma.length, Nat.add_assoc]
  · have hpos := FreeMagma.length_pos r.first
    simp only [weight_mul, FreeMagma.length]
    omega

theorem word_eq (r : Rotation n) :
    FreeMagma.toFreeSemigroup r.source = FreeMagma.toFreeSemigroup r.target := by
  apply r.context.plug_word_eq
  simp only [map_mul, mul_assoc]

end Rotation

theorem step_length_eq {s t : Term n} (h : Step s t) : s.length = t.length := by
  rcases h with ⟨r, rfl, rfl⟩
  exact r.length_eq

theorem step_weight_lt {s t : Term n} (h : Step s t) : weight t < weight s := by
  rcases h with ⟨r, rfl, rfl⟩
  exact r.weight_lt

theorem step_word_eq {s t : Term n} (h : Step s t) :
    FreeMagma.toFreeSemigroup s = FreeMagma.toFreeSemigroup t := by
  rcases h with ⟨r, rfl, rfl⟩
  exact r.word_eq

/-- Reachability by zero or more right rotations at arbitrary expression positions. -/
def Reachable : Term n → Term n → Prop := Relation.ReflTransGen Step

theorem reachable_weight_le {s t : Term n} (h : Reachable s t) :
    weight t ≤ weight s := by
  induction h with
  | refl => exact le_rfl
  | tail _ h ih => exact le_trans (le_of_lt (step_weight_lt h)) ih

theorem reachable_eq_or_weight_lt {s t : Term n} (h : Reachable s t) :
    s = t ∨ weight t < weight s := by
  cases h with
  | refl => exact Or.inl rfl
  | tail h e => exact Or.inr (lt_of_lt_of_le (step_weight_lt e) (reachable_weight_le h))

theorem reachable_antisymm {s t : Term n} (hst : Reachable s t)
    (hts : Reachable t s) : s = t := by
  rcases reachable_eq_or_weight_lt hst with h | h
  · exact h
  · exact False.elim ((not_lt_of_ge (reachable_weight_le hts)) h)

/-- The actual reassociation partial order on parenthesized matrix-valued expressions. -/
@[instance_reducible]
def rotationOrder : PartialOrder (Term n) where
  le := Reachable
  le_refl _ := Relation.ReflTransGen.refl
  le_trans _ _ _ := Relation.ReflTransGen.trans
  le_antisymm _ _ := reachable_antisymm

theorem reachable_length_eq {s t : Term n} (h : Reachable s t) : s.length = t.length := by
  induction h with
  | refl => rfl
  | tail _ h ih => exact ih.trans (step_length_eq h)

theorem reachable_word_eq {s t : Term n} (h : Reachable s t) :
    FreeMagma.toFreeSemigroup s = FreeMagma.toFreeSemigroup t := by
  induction h with
  | refl => rfl
  | tail _ h ih => exact ih.trans (step_word_eq h)

theorem step_no_reverse {s t : Term n} (h : Step s t) : ¬ Reachable t s := by
  intro hts
  exact (not_lt_of_ge (reachable_weight_le hts)) (step_weight_lt h)

theorem step_strict {s t : Term n} (h : Step s t) :
    @LT.lt (Term n) rotationOrder.toLT s t := by
  change Reachable s t ∧ ¬ Reachable t s
  exact ⟨Relation.ReflTransGen.single h, step_no_reverse h⟩

theorem different_words_incomparable {s t : Term n}
    (h : FreeMagma.toFreeSemigroup s ≠ FreeMagma.toFreeSemigroup t) :
    ¬ Reachable s t ∧ ¬ Reachable t s := by
  exact ⟨fun hst => h (reachable_word_eq hst), fun hts => h (reachable_word_eq hts).symm⟩

end InfoGeometry.Canonical.MatrixPeirceZorn.Zorn.Reassociation
