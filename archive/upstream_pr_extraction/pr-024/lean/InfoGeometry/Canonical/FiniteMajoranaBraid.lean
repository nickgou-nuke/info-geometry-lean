import Mathlib.Tactic

/-!
# InfoGeometry.Canonical.FiniteMajoranaBraid

Finite braid and parity lemmas for Boolean/Majorana mode registers.

This file proves only finite algebraic facts:

* adjacent swaps are involutions;
* the two adjacent swaps on a three-mode register satisfy the braid relation;
* disjoint adjacent swaps on a four-mode register commute;
* Boolean occupation parity is preserved by these swaps.

No infinite limit, operator-algebra completion, or analytic claim is made here.
-/

namespace InfoGeometry.Canonical.FiniteMajoranaBraid

/-! ## Three-mode local braid relation -/

/-- Swap the first two entries of a three-mode register. -/
def swap12 {α : Type*} : α × α × α → α × α × α
  | (a, b, c) => (b, a, c)

/-- Swap the last two entries of a three-mode register. -/
def swap23 {α : Type*} : α × α × α → α × α × α
  | (a, b, c) => (a, c, b)

@[simp]
theorem swap12_involutive {α : Type*} (x : α × α × α) :
    swap12 (swap12 x) = x := by
  rcases x with ⟨a, b, c⟩
  rfl

@[simp]
theorem swap23_involutive {α : Type*} (x : α × α × α) :
    swap23 (swap23 x) = x := by
  rcases x with ⟨a, b, c⟩
  rfl

/--
The finite three-mode braid relation.

On triples, adjacent swaps satisfy

`swap12 ∘ swap23 ∘ swap12 = swap23 ∘ swap12 ∘ swap23`.
-/
theorem swap12_swap23_swap12_eq_swap23_swap12_swap23
    {α : Type*} (x : α × α × α) :
    swap12 (swap23 (swap12 x)) = swap23 (swap12 (swap23 x)) := by
  rcases x with ⟨a, b, c⟩
  rfl

/-! ## Four-mode far commutation -/

/-- Swap the first two entries of a four-mode register. -/
def swap12₄ {α : Type*} : α × α × α × α → α × α × α × α
  | (a, b, c, d) => (b, a, c, d)

/-- Swap the last two entries of a four-mode register. -/
def swap34₄ {α : Type*} : α × α × α × α → α × α × α × α
  | (a, b, c, d) => (a, b, d, c)

@[simp]
theorem swap12₄_involutive {α : Type*} (x : α × α × α × α) :
    swap12₄ (swap12₄ x) = x := by
  rcases x with ⟨a, b, c, d⟩
  rfl

@[simp]
theorem swap34₄_involutive {α : Type*} (x : α × α × α × α) :
    swap34₄ (swap34₄ x) = x := by
  rcases x with ⟨a, b, c, d⟩
  rfl

/--
Disjoint adjacent swaps commute on a four-mode register.
-/
theorem swap12₄_swap34₄_commute {α : Type*} (x : α × α × α × α) :
    swap12₄ (swap34₄ x) = swap34₄ (swap12₄ x) := by
  rcases x with ⟨a, b, c, d⟩
  rfl

/-! ## Boolean charge/parity preservation -/

/-- Boolean occupation charge as an element of `ZMod 2`. -/
def bitCharge : Bool → ZMod 2
  | false => 0
  | true => 1

/-- Total `ZMod 2` occupation parity of a three-mode Boolean register. -/
def parity3 : Bool × Bool × Bool → ZMod 2
  | (a, b, c) => bitCharge a + bitCharge b + bitCharge c

/-- Total `ZMod 2` occupation parity of a four-mode Boolean register. -/
def parity4 : Bool × Bool × Bool × Bool → ZMod 2
  | (a, b, c, d) => bitCharge a + bitCharge b + bitCharge c + bitCharge d

@[simp]
theorem parity3_swap12 (x : Bool × Bool × Bool) :
    parity3 (swap12 x) = parity3 x := by
  rcases x with ⟨a, b, c⟩
  cases a <;> cases b <;> cases c <;> native_decide

@[simp]
theorem parity3_swap23 (x : Bool × Bool × Bool) :
    parity3 (swap23 x) = parity3 x := by
  rcases x with ⟨a, b, c⟩
  cases a <;> cases b <;> cases c <;> native_decide

@[simp]
theorem parity4_swap12₄ (x : Bool × Bool × Bool × Bool) :
    parity4 (swap12₄ x) = parity4 x := by
  rcases x with ⟨a, b, c, d⟩
  cases a <;> cases b <;> cases c <;> cases d <;> native_decide

@[simp]
theorem parity4_swap34₄ (x : Bool × Bool × Bool × Bool) :
    parity4 (swap34₄ x) = parity4 x := by
  rcases x with ⟨a, b, c, d⟩
  cases a <;> cases b <;> cases c <;> cases d <;> native_decide

/--
The three-mode braid word preserves Boolean occupation parity.
-/
theorem parity3_braid_word_left (x : Bool × Bool × Bool) :
    parity3 (swap12 (swap23 (swap12 x))) = parity3 x := by
  simp

/--
The opposite three-mode braid word preserves the same Boolean occupation parity.
-/
theorem parity3_braid_word_right (x : Bool × Bool × Bool) :
    parity3 (swap23 (swap12 (swap23 x))) = parity3 x := by
  simp

end InfoGeometry.Canonical.FiniteMajoranaBraid
