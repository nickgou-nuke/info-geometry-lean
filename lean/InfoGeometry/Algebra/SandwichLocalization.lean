/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Algebra.Colimit.DirectLimit
import Mathlib.Algebra.Module.Equiv.Basic
import Mathlib.Algebra.Ring.Subring.Basic
import Mathlib.Tactic.NoncommRing
import Lean.Elab.Tactic.Omega

/-!
# Two-sided additive localization at one noncentral denominator

The carrier is the native directed limit of the additive groups of `B`, indexed
by `ℕ × ℕ`. The transition maps multiply on the left and right, retaining the
order of every ambient product. No Ore condition or centrality in `B` is used.
Regularity is needed for the exact cross-product criterion and faithful
embedding, not for construction of the directed limit itself.
-/

namespace InfoGeometry.Algebra.SandwichLocalization

variable {B : Type*} [Ring B]

/-- The additive transition from `(k,l)` to `(k+a,l+b)`. -/
def transition (s : B) (i j : ℕ × ℕ) (_h : i ≤ j) : B →+ B where
  toFun x := s ^ (j.1 - i.1) * x * s ^ (j.2 - i.2)
  map_zero' := by simp
  map_add' x y := by simp only [mul_add, add_mul]

@[simp] theorem transition_apply (s : B) (i j : ℕ × ℕ) (h : i ≤ j) (x : B) :
    transition s i j h x = s ^ (j.1 - i.1) * x * s ^ (j.2 - i.2) := rfl

instance directedSystem (s : B) :
    DirectedSystem (fun _ : ℕ × ℕ => B) (fun i j h => transition s i j h) where
  map_self x := by simp
  map_map {k j i} hij hjk x := by
    change s ^ (k.1 - j.1) * (s ^ (j.1 - i.1) * x * s ^ (j.2 - i.2)) *
      s ^ (k.2 - j.2) = s ^ (k.1 - i.1) * x * s ^ (k.2 - i.2)
    calc
      _ = (s ^ (k.1 - j.1) * s ^ (j.1 - i.1)) * x *
          (s ^ (j.2 - i.2) * s ^ (k.2 - j.2)) := by noncomm_ring
      _ = s ^ ((k.1 - j.1) + (j.1 - i.1)) * x *
          s ^ ((j.2 - i.2) + (k.2 - j.2)) := by rw [← pow_add, ← pow_add]
      _ = _ := by
        have h₁ : k.1 - j.1 + (j.1 - i.1) = k.1 - i.1 := by
          have := hij.1; have := hjk.1; omega
        have h₂ : j.2 - i.2 + (k.2 - j.2) = k.2 - i.2 := by
          have := hij.2; have := hjk.2; omega
        rw [h₁, h₂]

/-- The actual native additive direct limit, with independent denominator indices. -/
abbrev Space (s : B) :=
  DirectLimit (fun _ : ℕ × ℕ => B) (transition s)

/-- The representative of `s⁻ᵏ x s⁻ˡ`; inverse notation is mnemonic only. -/
def repr (s : B) (k : ℕ) (x : B) (l : ℕ) : Space s := ⟦⟨(k, l), x⟩⟧

theorem exists_repr (s : B) (z : Space s) :
    ∃ k x l, repr s k x l = z := by
  induction z using DirectLimit.induction with
  | ih i x => exact ⟨i.1, x, i.2, rfl⟩

/-- Enlarge either denominator and multiply the corresponding side of the numerator. -/
theorem repr_bond (s : B) (k l a b : ℕ) (x : B) :
    repr s (k + a) (s ^ a * x * s ^ b) (l + b) = repr s k x l := by
  have h : (k, l) ≤ (k + a, l + b) := ⟨Nat.le_add_right _ _, Nat.le_add_right _ _⟩
  simpa only [transition_apply, Nat.add_sub_cancel_left] using
    (DirectLimit.mk_apply (f := transition s) (k, l) (k + a, l + b) x h)

@[simp] theorem repr_zero (s : B) (k l : ℕ) : repr s k 0 l = 0 :=
  (DirectLimit.zero_def (f := transition s) (k, l)).symm

/-- Equal-stage addition is inherited from the native additive direct limit. -/
theorem repr_add_same (s : B) (k l : ℕ) (x y : B) :
    repr s k (x + y) l = repr s k x l + repr s k y l :=
  (DirectLimit.add_def (f := transition s) (k, l) x y).symm

/-- Native additive stage maps. -/
def stage (s : B) (k l : ℕ) : B →+ Space s where
  toFun x := repr s k x l
  map_zero' := repr_zero s k l
  map_add' := repr_add_same s k l

@[simp] theorem stage_apply (s : B) (k l : ℕ) (x : B) :
    stage s k l x = repr s k x l := rfl

/-- The submitted common-denominator formula, on the constructed carrier. -/
theorem repr_add (s : B) (k l k' l' : ℕ) (x y : B) :
    repr s k x l + repr s k' y l' =
      repr s (k + k') (s ^ k' * x * s ^ l' + s ^ k * y * s ^ l) (l + l') := by
  calc
    _ = repr s (k + k') (s ^ k' * x * s ^ l') (l + l') +
        repr s (k + k') (s ^ k * y * s ^ l) (l + l') := by
      congr 1
      · exact (repr_bond s k l k' l' x).symm
      · simpa only [Nat.add_comm] using (repr_bond s k' l' k l y).symm
    _ = _ := (repr_add_same s (k + k') (l + l') _ _).symm

@[simp] theorem repr_neg (s : B) (k l : ℕ) (x : B) :
    repr s k (-x) l = -repr s k x l := (stage s k l).map_neg x

/-- The direct-limit equality criterion before imposing regularity. -/
theorem repr_eq_iff_common_stage (s : B) (k l k' l' : ℕ) (x y : B) :
    repr s k x l = repr s k' y l' ↔
      ∃ a b, k ≤ a ∧ l ≤ b ∧ k' ≤ a ∧ l' ≤ b ∧
        s ^ (a - k) * x * s ^ (b - l) =
          s ^ (a - k') * y * s ^ (b - l') := by
  change (⟦⟨(k, l), x⟩⟧ : Space s) = ⟦⟨(k', l'), y⟩⟧ ↔ _
  rw [Quotient.eq]
  constructor
  · rintro ⟨⟨a, b⟩, h, h', he⟩
    exact ⟨a, b, h.1, h.2, h'.1, h'.2, he⟩
  · rintro ⟨a, b, hk, hl, hk', hl', he⟩
    exact ⟨(a, b), ⟨hk, hl⟩, ⟨hk', hl'⟩, he⟩

theorem pow_left_injective (s : B) (hs : Function.Injective (s * ·)) (n : ℕ) :
    Function.Injective (s ^ n * ·) := by
  induction n with
  | zero => simpa only [pow_zero, one_mul] using (Function.injective_id : Function.Injective (id : B → B))
  | succ n hn =>
      intro x y h
      apply hn
      apply hs
      simpa only [pow_succ', mul_assoc] using h

theorem pow_right_injective (s : B) (hs : Function.Injective (· * s)) (n : ℕ) :
    Function.Injective (· * s ^ n) := by
  induction n with
  | zero => simpa only [pow_zero, mul_one] using (Function.injective_id : Function.Injective (id : B → B))
  | succ n hn =>
      intro x y h
      apply hn
      apply hs
      simpa only [pow_succ, ← mul_assoc] using h

/-- Faithfulness follows from regularity on both sides of the denominator. -/
theorem stage_injective (s : B)
    (hleft : Function.Injective (s * ·)) (hright : Function.Injective (· * s))
    (k l : ℕ) : Function.Injective (stage s k l) := by
  apply DirectLimit.mk_injective
  intro i j h x y he
  apply pow_left_injective s hleft (j.1 - i.1)
  apply pow_right_injective s hright (j.2 - i.2)
  exact he

/-- Clearing denominators is exact for a two-sided regular element. -/
theorem repr_eq_iff_cross (s : B)
    (hleft : Function.Injective (s * ·)) (hright : Function.Injective (· * s))
    (k l k' l' : ℕ) (x y : B) :
    repr s k x l = repr s k' y l' ↔
      s ^ k' * x * s ^ l' = s ^ k * y * s ^ l := by
  constructor
  · intro he
    have h₁ := (repr_bond s k l k' l' x).trans he
    have h₂ := repr_bond s k' l' k l y
    have he' : repr s (k + k') (s ^ k' * x * s ^ l') (l + l') =
        repr s (k + k') (s ^ k * y * s ^ l) (l + l') := by
      simpa only [Nat.add_comm] using h₁.trans h₂.symm
    exact stage_injective s hleft hright (k + k') (l + l') he'
  · intro he
    calc
      _ = repr s (k + k') (s ^ k' * x * s ^ l') (l + l') :=
        (repr_bond s k l k' l' x).symm
      _ = repr s (k + k') (s ^ k * y * s ^ l) (l + l') := by rw [he]
      _ = _ := by simpa only [Nat.add_comm] using repr_bond s k' l' k l y

/-- The original ambient additive group embeds at stage `(0,0)`. -/
abbrev of (s : B) : B →+ Space s := stage s 0 0

theorem of_injective (s : B)
    (hleft : Function.Injective (s * ·)) (hright : Function.Injective (· * s)) :
    Function.Injective (of s) := stage_injective s hleft hright 0 0

section Universal

variable {F : Type*} [AddCommGroup F]

/-- The additive universal map from any compatible two-index cocone. -/
noncomputable def additiveDesc (s : B) (f : ℕ → ℕ → B →+ F)
    (hf : ∀ k l a b x, f (k + a) (l + b) (s ^ a * x * s ^ b) = f k l x) :
    Space s →+ F where
  toFun := DirectLimit.lift (transition s) (fun i x => f i.1 i.2 x) (by
    intro i j h x
    have h₁ : i.1 + (j.1 - i.1) = j.1 := Nat.add_sub_of_le h.1
    have h₂ : i.2 + (j.2 - i.2) = j.2 := Nat.add_sub_of_le h.2
    simpa only [transition_apply, h₁, h₂] using
      (hf i.1 i.2 (j.1 - i.1) (j.2 - i.2) x).symm)
  map_zero' := by
    rw [DirectLimit.zero_def (f := transition s) (0, 0), DirectLimit.lift_def, map_zero]
  map_add' x y := by
    induction x, y using DirectLimit.induction₂ with
    | ih i x y =>
      rw [DirectLimit.add_def, DirectLimit.lift_def, DirectLimit.lift_def,
        DirectLimit.lift_def, map_add]

@[simp] theorem additiveDesc_repr (s : B) (f : ℕ → ℕ → B →+ F)
    (hf : ∀ k l a b x, f (k + a) (l + b) (s ^ a * x * s ^ b) = f k l x)
    (k l : ℕ) (x : B) : additiveDesc s f hf (repr s k x l) = f k l x := rfl

theorem additiveDesc_unique (s : B) (f : ℕ → ℕ → B →+ F)
    (hf : ∀ k l a b x, f (k + a) (l + b) (s ^ a * x * s ^ b) = f k l x)
    (g : Space s →+ F) (hg : ∀ k l x, g (repr s k x l) = f k l x) :
    g = additiveDesc s f hf := by
  ext z
  obtain ⟨k, x, l, rfl⟩ := exists_repr s z
  rw [hg, additiveDesc_repr]

theorem existsUnique_additiveDesc (s : B) (f : ℕ → ℕ → B →+ F)
    (hf : ∀ k l a b x, f (k + a) (l + b) (s ^ a * x * s ^ b) = f k l x) :
    ∃! g : Space s →+ F, ∀ k l x, g (repr s k x l) = f k l x := by
  exact ⟨additiveDesc s f hf, additiveDesc_repr s f hf,
    fun g hg => additiveDesc_unique s f hf g hg⟩

end Universal

end InfoGeometry.Algebra.SandwichLocalization
