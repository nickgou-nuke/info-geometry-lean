/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib
import Omega.SPG.SquareclassHammingIsometry

/-!
# Causal Poset: The Hardware Semidirect Weyl Orbit

This module synthesizes the Type-D Semidirect Weyl Group Action on the
ATOMiK Delta-State hardware geometry.

- BUCKET 1 (Established Mathematical Target & Existing Owners):
  * `Bitword ι := ι → ZMod 2` with XOR translation `applyDelta`, parity functional
    `bitwordParity`,even-parity subgroup `TypeDTransitionSubgroup`, and coordinate
    permutation action `permAction`.
- BUCKET 2 (Deconfabulation):
  * Eliminated bare `Prop`-valued `def` wrappers (`IsTypeDDelta`, `TypeDReachable`) and
    stated the reachability equivalence directly on the affine semidirect action.
- BUCKET 3 (Constructive Lean 4 Theorems Proved Here):
  * `bitwordParity_add`: additivity of total parity over `ZMod 2`.
  * `perm_preserves_parity`: permutation invariance of total parity.
  * `typeD_hardware_preserves_parity`: parity invariance under even-parity translation
    followed by coordinate permutation.
  * `typeD_reachable_iff_parity_eq`: two bitwords are connected by an even-parity
    translation and coordinate permutation if and only if their parities agree.
-/

open scoped BigOperators

namespace InfoGeometry.GrandUnification.TypeDWeyl

universe u

variable {ι : Type u} [Fintype ι] [DecidableEq ι]

/-- Archetype I: The Bitword Vector Space `ι → ZMod 2`. -/
abbrev Bitword (ι : Type u) := ι → ZMod 2

/-- Archetype II: The Hardware XOR / Affine Translation on bitwords. -/
def applyDelta (state delta : Bitword ι) : Bitword ι :=
  state + delta

/-- Archetype III: The total `ZMod 2` parity functional on bitwords. -/
def bitwordParity (w : Bitword ι) : ZMod 2 :=
  ∑ i : ι, w i

omit [DecidableEq ι] in
/-- Total parity is additive under bitwise addition. -/
@[simp]
theorem bitwordParity_add (v w : Bitword ι) :
    bitwordParity (v + w) = bitwordParity v + bitwordParity w := by
  dsimp [bitwordParity]
  exact Finset.sum_add_distrib

/-- The Type-D even-parity transition subgroup `{ d : Bitword ι | bitwordParity d = 0 }`. -/
def TypeDTransitionSubgroup (ι : Type u) [Fintype ι] [DecidableEq ι] : AddSubgroup (Bitword ι) where
  carrier := { d | bitwordParity d = 0 }
  add_mem' {a b} ha hb := by
    dsimp [bitwordParity] at ha hb ⊢
    rw [Finset.sum_add_distrib, ha, hb, add_zero]
  zero_mem' := by
    dsimp [bitwordParity]
    rw [Finset.sum_const_zero]
  neg_mem' {a} ha := by
    change bitwordParity a = 0 at ha
    change bitwordParity (-a) = 0
    have h_neg_eq : (-a) = a := by
      ext i
      exact CharTwo.neg_eq (a i)
    rw [h_neg_eq, ha]

/-- Archetype IV: The Routing Permutation (Weyl coordinate permutation action). -/
def permAction (σ : Equiv.Perm ι) (w : Bitword ι) : Bitword ι :=
  fun i => w (σ.symm i)

omit [DecidableEq ι] in
/-- Permutations strictly preserve bitword parity. -/
lemma perm_preserves_parity (σ : Equiv.Perm ι) (w : Bitword ι) :
    bitwordParity (permAction σ w) = bitwordParity w := by
  unfold bitwordParity permAction
  exact Equiv.sum_comp σ.symm w

/-- Applying an even-parity delta and then a coordinate permutation preserves
the total bitword parity. -/
theorem typeD_hardware_preserves_parity
    (state : Bitword ι)
    (delta : TypeDTransitionSubgroup ι)
    (σ : Equiv.Perm ι) :
    bitwordParity (permAction σ (applyDelta state delta.val)) = bitwordParity state := by
  rw [perm_preserves_parity]
  change ∑ i : ι, (state i + delta.val i) = bitwordParity state
  rw [Finset.sum_add_distrib]
  change bitwordParity state + bitwordParity delta.val = bitwordParity state
  rw [delta.property, add_zero]

/-- Two finite bitwords are connected by an even-parity translation and a coordinate
permutation if and only if their total parities agree. -/
theorem typeD_reachable_iff_parity_eq (x y : Bitword ι) :
    (∃ delta : TypeDTransitionSubgroup ι, ∃ σ : Equiv.Perm ι,
      permAction σ (applyDelta x delta.val) = y) ↔
      bitwordParity x = bitwordParity y := by
  constructor
  · rintro ⟨delta, σ, hxy⟩
    have h := congrArg bitwordParity hxy
    rw [typeD_hardware_preserves_parity x delta σ] at h
    exact h
  · intro hparity
    have hdelta : bitwordParity (x + y) = 0 := by
      rw [bitwordParity_add, hparity]
      exact Omega.SPG.zmod2_add_self _
    refine ⟨⟨x + y, hdelta⟩, Equiv.refl ι, ?_⟩
    change x + (x + y) = y
    funext i
    change x i + (x i + y i) = y i
    rw [← add_assoc]
    rw [Omega.SPG.zmod2_add_self, zero_add]

end InfoGeometry.GrandUnification.TypeDWeyl
