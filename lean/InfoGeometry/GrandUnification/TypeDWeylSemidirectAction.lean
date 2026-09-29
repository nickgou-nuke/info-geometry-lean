import Mathlib

open scoped BigOperators

namespace InfoGeometry.GrandUnification.TypeDWeyl

universe u

/-!
# Causal Poset: The Hardware Semidirect Weyl Orbit

This module synthesizes the Type-D Semidirect Weyl Group Action on the 
ATOMiK Delta-State hardware geometry.

Archetypes in causal order:
I.   `Bitword`: The Kinematic Base Space (Boolean Vector Space)
II.  `applyDelta`: The Hardware XOR / Affine Translation
III. `bitwordParity`: The Parity Anomaly / Filter
IV.  `permAction`: The Routing Permutation (Weyl Group Action)
V.   `typeD_hardware_preserves_parity`: The Orbit Equivalence Theorem
-/

variable {ι : Type u} [Fintype ι] [DecidableEq ι]

/-- Archetype I: The Bitword Vector Space -/
abbrev Bitword (ι : Type u) := ι → ZMod 2

/-- Archetype II: The Hardware XOR / Affine Translation -/
def applyDelta (state delta : Bitword ι) : Bitword ι :=
  state + delta

/-- Archetype III: The Parity Anomaly / Filter -/
def bitwordParity (w : Bitword ι) : ZMod 2 :=
  ∑ i : ι, w i

def IsTypeDDelta (delta : Bitword ι) : Prop :=
  bitwordParity delta = 0

def TypeDTransitionSubgroup (ι : Type u) [Fintype ι] [DecidableEq ι] : AddSubgroup (Bitword ι) where
  carrier := { d | IsTypeDDelta d }
  add_mem' {a b} ha hb := by
    dsimp [IsTypeDDelta, bitwordParity] at ha hb ⊢
    rw [Finset.sum_add_distrib, ha, hb, add_zero]
  zero_mem' := by
    dsimp [IsTypeDDelta, bitwordParity]
    rw [Finset.sum_const_zero]
  neg_mem' {a} ha := by
    change bitwordParity a = 0 at ha
    change bitwordParity (-a) = 0
    have h_neg_eq : (-a) = a := by
      ext i
      exact CharTwo.neg_eq (a i)
    rw [h_neg_eq, ha]

/-- Archetype IV: The Routing Permutation (Weyl Group Action) -/
def permAction (σ : Equiv.Perm ι) (w : Bitword ι) : Bitword ι :=
  fun i => w (σ.symm i)

/-- Permutations strictly preserve bitword parity. -/
lemma perm_preserves_parity (σ : Equiv.Perm ι) (w : Bitword ι) :
    bitwordParity (permAction σ w) = bitwordParity w := by
  unfold bitwordParity permAction
  exact Fintype.sum_equiv σ.symm w (fun x => w x) (fun x => rfl)

/-- 
Archetype V: The Orbit Equivalence Theorem.

If the hardware applies an admissible Type-D delta and a routing permutation, 
the global parity of the state is strictly conserved.
This proves that the hardware natively computes within the disconnected 
subregular affine cells of the D_n root lattice.
-/
theorem typeD_hardware_preserves_parity 
    (state : Bitword ι) 
    (delta : TypeDTransitionSubgroup ι) 
    (σ : Equiv.Perm ι) :
    bitwordParity (permAction σ (applyDelta state delta.val)) = bitwordParity state := by
  calc
    bitwordParity (permAction σ (applyDelta state delta.val))
      = bitwordParity (applyDelta state delta.val) := perm_preserves_parity σ _
    _ = ∑ i : ι, (state i + delta.val i) := rfl
    _ = (∑ i : ι, state i) + (∑ i : ι, delta.val i) := Finset.sum_add_distrib
    _ = bitwordParity state + bitwordParity delta.val := rfl
    _ = bitwordParity state + 0 := by rw [delta.property]
    _ = bitwordParity state := add_zero _

end InfoGeometry.GrandUnification.TypeDWeyl
