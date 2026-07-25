import Mathlib.Tactic
import Mathlib.Order.Category.BoolAlg

/-!
# Mathlib-native Stone bridge for Boolean algebras

Canonical theorem-proved Stone point layer: ultrafilters on a Boolean algebra
are equivalent to mathlib bounded lattice homomorphisms into the two-element
Boolean algebra `Bool`.

This file intentionally proves only the algebraic Stone core and basic clopen
identities.  It does not assert compactness, Radon extension, AF C*-completion,
MASA spectra, motives, or amplituhedron statements.
-/

noncomputable section

namespace InfoGeometry.Canonical.StoneBridgeMathlib

open Set

/-- Order-theoretic ultrafilter on an arbitrary Boolean algebra. -/
structure BooleanUltrafilter (B : Type*) [BooleanAlgebra B] where
  carrier : Set B
  top_mem : ⊤ ∈ carrier
  inf_mem : ∀ {a b : B}, a ∈ carrier → b ∈ carrier → a ⊓ b ∈ carrier
  upward : ∀ {a b : B}, a ∈ carrier → a ≤ b → b ∈ carrier
  bot_not_mem : ⊥ ∉ carrier
  mem_or_compl_mem : ∀ a : B, a ∈ carrier ∨ aᶜ ∈ carrier

namespace BooleanUltrafilter

variable {B : Type*} [BooleanAlgebra B]

@[ext] theorem ext {U V : BooleanUltrafilter B} (h : U.carrier = V.carrier) : U = V := by
  cases U
  cases V
  simp_all

/-- An ultrafilter cannot contain both an element and its Boolean complement. -/
theorem compl_not_mem_of_mem (U : BooleanUltrafilter B) {a : B} (ha : a ∈ U.carrier) :
    aᶜ ∉ U.carrier := by
  intro hca
  have hbot : (⊥ : B) ∈ U.carrier := by
    have h := U.inf_mem ha hca
    simpa using h
  exact U.bot_not_mem hbot

/-- Membership of a complement is equivalent to nonmembership. -/
theorem compl_mem_iff_not_mem (U : BooleanUltrafilter B) (a : B) :
    aᶜ ∈ U.carrier ↔ a ∉ U.carrier := by
  constructor
  · intro hca ha
    exact U.bot_not_mem (by simpa using U.inf_mem ha hca)
  · intro hna
    rcases U.mem_or_compl_mem a with ha | hca
    · exact (hna ha).elim
    · exact hca

/-- Membership of an infimum is conjunction of memberships. -/
theorem inf_mem_iff (U : BooleanUltrafilter B) (a b : B) :
    a ⊓ b ∈ U.carrier ↔ a ∈ U.carrier ∧ b ∈ U.carrier := by
  constructor
  · intro hab
    exact ⟨U.upward hab inf_le_left, U.upward hab inf_le_right⟩
  · intro h
    exact U.inf_mem h.1 h.2

/-- Membership of a supremum is disjunction of memberships. -/
theorem sup_mem_iff (U : BooleanUltrafilter B) (a b : B) :
    a ⊔ b ∈ U.carrier ↔ a ∈ U.carrier ∨ b ∈ U.carrier := by
  constructor
  · intro hab
    by_contra hnone
    have hna : a ∉ U.carrier := by intro ha; exact hnone (Or.inl ha)
    have hnb : b ∉ U.carrier := by intro hb; exact hnone (Or.inr hb)
    have hca : aᶜ ∈ U.carrier := (U.compl_mem_iff_not_mem a).2 hna
    have hcb : bᶜ ∈ U.carrier := (U.compl_mem_iff_not_mem b).2 hnb
    have hc : (a ⊔ b)ᶜ ∈ U.carrier := by
      have h := U.inf_mem hca hcb
      simpa [compl_sup] using h
    have hI := U.inf_mem hab hc
    have hEq : (a ⊔ b) ⊓ (aᶜ ⊓ bᶜ) = (⊥ : B) := by
      rw [← compl_sup]
      exact inf_compl_self (a ⊔ b)
    exact U.bot_not_mem (by simpa [compl_sup, hEq] using hI)
  · intro h
    rcases h with ha | hb
    · exact U.upward ha le_sup_left
    · exact U.upward hb le_sup_right

/-- Mathlib-native two-valued Boolean homomorphisms. -/
abbrev BooleanPointHom (B : Type*) [BooleanAlgebra B] := BoundedLatticeHom B Bool

/-- Characteristic homomorphism of an ultrafilter into the two-element Boolean algebra. -/
def toBooleanPointHom (U : BooleanUltrafilter B) : BooleanPointHom B :=
  BoundedLatticeHom.mk
    (LatticeHom.mk
      (SupHom.mk
        (fun a => @ite Bool (a ∈ U.carrier) (Classical.propDecidable (a ∈ U.carrier)) true false)
        (by
          intro a b
          by_cases ha : a ∈ U.carrier <;> by_cases hb : b ∈ U.carrier
          · have hab : a ⊔ b ∈ U.carrier := (U.sup_mem_iff a b).2 (Or.inl ha)
            simp [ha, hb, hab]
          · have hab : a ⊔ b ∈ U.carrier := (U.sup_mem_iff a b).2 (Or.inl ha)
            simp [ha, hb, hab]
          · have hab : a ⊔ b ∈ U.carrier := (U.sup_mem_iff a b).2 (Or.inr hb)
            simp [ha, hb, hab]
          · have hab : a ⊔ b ∉ U.carrier := by
              intro h
              exact (U.sup_mem_iff a b).1 h |>.elim ha hb
            simp [ha, hb, hab]))
      (by
        intro a b
        by_cases ha : a ∈ U.carrier <;> by_cases hb : b ∈ U.carrier
        · have hab : a ⊓ b ∈ U.carrier := (U.inf_mem_iff a b).2 ⟨ha, hb⟩
          simp [ha, hb, hab]
        · have hab : a ⊓ b ∉ U.carrier := by
            intro h
            exact hb ((U.inf_mem_iff a b).1 h).2
          simp [ha, hb, hab]
        · have hab : a ⊓ b ∉ U.carrier := by
            intro h
            exact ha ((U.inf_mem_iff a b).1 h).1
          simp [ha, hb, hab]
        · have hab : a ⊓ b ∉ U.carrier := by
            intro h
            exact ha ((U.inf_mem_iff a b).1 h).1
          simp [ha, hb, hab]))
    (by simpa using U.top_mem)
    (by
      by_cases h : (⊥ : B) ∈ U.carrier
      · exact (U.bot_not_mem h).elim
      · simp [h])

@[simp] theorem toBooleanPointHom_apply (U : BooleanUltrafilter B) (a : B) :
    U.toBooleanPointHom a =
      @ite Bool (a ∈ U.carrier) (Classical.propDecidable (a ∈ U.carrier)) true false :=
  rfl

/-- The ultrafilter induced by a mathlib bounded lattice homomorphism `B → Bool`. -/
def ofBooleanPointHom (f : BooleanPointHom B) : BooleanUltrafilter B where
  carrier := {a | f a = true}
  top_mem := by simp [map_top f]
  inf_mem := by
    intro a b ha hb
    change f a = true at ha
    change f b = true at hb
    show f (a ⊓ b) = true
    rw [map_inf]
    simp [ha, hb]
  upward := by
    intro a b ha hab
    change f a = true at ha
    have hsup : a ⊔ b = b := sup_eq_right.2 hab
    have hsupmem : f (a ⊔ b) = true := by
      rw [map_sup]
      simp [ha]
    simpa [hsup] using hsupmem
  bot_not_mem := by
    intro hbot
    change f (⊥ : B) = true at hbot
    have hb : f (⊥ : B) = (⊥ : Bool) := map_bot f
    rw [hbot] at hb
    simp at hb
  mem_or_compl_mem := by
    intro a
    by_cases ha : f a = true
    · exact Or.inl ha
    · have hf : f a = false := by cases h : f a <;> simp [h] at ha ⊢
      have hc : f aᶜ = true := by
        rw [map_compl']
        simp [hf]
      exact Or.inr hc

@[simp] theorem mem_ofBooleanPointHom (f : BooleanPointHom B) (a : B) :
    a ∈ (ofBooleanPointHom f : BooleanUltrafilter B).carrier ↔ f a = true :=
  Iff.rfl

/-- Recover an ultrafilter from its characteristic homomorphism. -/
theorem of_toBooleanPointHom (U : BooleanUltrafilter B) :
    ofBooleanPointHom U.toBooleanPointHom = U := by
  ext a
  simp [ofBooleanPointHom]

/-- Recover a homomorphism from its induced ultrafilter. -/
theorem to_ofBooleanPointHom (f : BooleanPointHom B) :
    (ofBooleanPointHom f).toBooleanPointHom = f := by
  ext a
  by_cases ha : f a = true
  · simp [toBooleanPointHom, ofBooleanPointHom, ha]
  · have hf : f a = false := by cases h : f a <;> simp [h] at ha ⊢
    simp [toBooleanPointHom, ofBooleanPointHom, hf]

/-- Canonical Stone-point theorem: ultrafilters are two-valued Boolean homomorphisms. -/
def stonePointEquivBooleanHom : BooleanUltrafilter B ≃ BooleanPointHom B where
  toFun := toBooleanPointHom
  invFun := ofBooleanPointHom
  left_inv := of_toBooleanPointHom
  right_inv := to_ofBooleanPointHom

/-- Basic Stone clopen set associated to `a : B`. -/
def stoneBasic (a : B) : Set (BooleanUltrafilter B) :=
  {U | a ∈ U.carrier}

@[simp] theorem mem_stoneBasic (U : BooleanUltrafilter B) (a : B) :
    U ∈ stoneBasic a ↔ a ∈ U.carrier :=
  Iff.rfl

/-- Stone basic opens preserve finite meets as intersections. -/
theorem stoneBasic_inf (a b : B) :
    stoneBasic (a ⊓ b) = stoneBasic a ∩ stoneBasic b := by
  ext U
  exact U.inf_mem_iff a b

/-- Stone basic opens preserve finite joins as unions. -/
theorem stoneBasic_sup (a b : B) :
    stoneBasic (a ⊔ b) = stoneBasic a ∪ stoneBasic b := by
  ext U
  exact U.sup_mem_iff a b

/-- Stone basic opens preserve complements as set complements. -/
theorem stoneBasic_compl (a : B) :
    stoneBasic aᶜ = (stoneBasic a)ᶜ := by
  ext U
  exact U.compl_mem_iff_not_mem a

end BooleanUltrafilter

end InfoGeometry.Canonical.StoneBridgeMathlib
