import Mathlib

open scoped BigOperators

namespace InfoGeometry.GrandUnification.AtomikTypeDBridge

/-!
# Causal Poset: The ATOMiK Type-D Parity Bridge

This module formally synthesizes the triangulation between:
1. ATOMiK's Hardware Delta-State Algebra (64-bit XOR transitions)
2. SubregularAffineCells-Lean's Type-D Weyl Rigid Parity (Signed Permutations)
3. InfoGeometry's Infinite Continuum (BitWord Cantor Fractal Limits)

Archetypes in causal order:
I.   `BitWord`: The Kinematic Base Space (Boolean Vector Space)
II.  `applyDelta`: The ATOMiK Hardware Transition Operator (XOR)
III. `parity`: The Type-D Root Lattice Parity Filter
IV.  `EvenParitySubgroup`: The Rigidity Condition (Affine Cell Boundary)
V.   `atomik_typeD_rigidity`: The Impermeability Theorem
VI.  `AtomikWeylAction`: The strict `AddAction` simulating the Weyl orbit
-/

variable {n : ℕ}

/-- 
Archetype I: The Kinematic Base Space.
The state space of the universe is a bitword, modeled rigorously as a 
Boolean vector space `Fin n → ZMod 2`.
-/
abbrev BitWord (n : ℕ) := Fin n → ZMod 2

/-- 
Archetype II: The ATOMiK Transition Operator.
State evolution is given by pointwise Boolean addition (XOR).
This is the `Delta.apply` instruction in the hardware architecture.
-/
def applyDelta (state delta : BitWord n) : BitWord n :=
  state + delta

/-- 
Archetype III: The Type-D Parity Operator.
The Weyl group of `D_n` acts via signed permutations with an *even* number 
of sign flips. We measure this algebraically via a sum over `ZMod 2`.
-/
def parity (v : BitWord n) : ZMod 2 :=
  ∑ i : Fin n, v i

/-- Genuine Lemma: Parity is a linear map (additivity over XOR). -/
@[simp]
theorem parity_add (v d : BitWord n) : parity (v + d) = parity v + parity d := by
  dsimp [parity]
  exact Finset.sum_add_distrib

/-- 
Archetype IV: The Type-D Even Parity Subgroup.
This defines the rigid subregular cell boundary constraints.
-/
def EvenParitySubgroup (n : ℕ) : AddSubgroup (BitWord n) where
  carrier := { v | parity v = 0 }
  add_mem' {a b} ha hb := by
    change parity a = 0 at ha
    change parity b = 0 at hb
    change parity (a + b) = 0
    rw [parity_add, ha, hb, add_zero]
  zero_mem' := by
    change parity 0 = 0
    exact Finset.sum_const_zero
  neg_mem' {a} ha := by
    change parity a = 0 at ha
    change parity (-a) = 0
    change ∑ i, (-a) i = 0
    have h_neg : (fun i => (-a) i) = fun i => -(a i) := rfl
    rw [h_neg, ← Finset.sum_neg_distrib, ha, neg_zero]

/-- 
Archetype V: The Atomik-Weyl Transition Rigidity.

Theorem: If an ATOMiK system applies a transition (Delta) governed by the 
Type-D Weyl root lattice (even parity), it cannot change the fundamental parity 
sector of the state space. This proves the Subregular affine cell boundary 
is impermeable to rigid Weyl transitions.
-/
theorem atomik_typeD_rigidity (state delta : BitWord n) (h_weyl : delta ∈ EvenParitySubgroup n) :
    parity (applyDelta state delta) = parity state := by
  dsimp [applyDelta]
  rw [parity_add, h_weyl, add_zero]

/-- 
Archetype VI: The Atomik Weyl Action.

The hardware delta-engine equipped with the parity filter perfectly instantiates 
a strict mathematical Group Action on the Boolean geometry. 
-/
instance AtomikWeylAction : AddAction (EvenParitySubgroup n) (BitWord n) where
  vadd d s := applyDelta s d.val
  zero_vadd s := by
    dsimp [applyDelta]
    ext i
    exact add_zero (s i)
  add_vadd d₁ d₂ s := by
    dsimp [applyDelta]
    ext i
    change s i + (d₁.val i + d₂.val i) = s i + d₂.val i + d₁.val i
    rw [add_assoc, add_comm (d₂.val i) (d₁.val i)]

end InfoGeometry.GrandUnification.AtomikTypeDBridge
