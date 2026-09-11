import Mathlib.Algebra.Group.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Data.List.Basic
import Mathlib.Data.Set.Basic

/-!
# Bruhat Partial Order via Subword Selection on Reduced Expressions

This module formalizes the strong Bruhat partial order on Coxeter systems `(W, S)` via
the subword property (Chevalley-Matsumoto-Tits characterization).

Proves reflexivity, identity minimality, subword dichotomy under generator peeling,
length preservation, and antisymmetry with zero axioms and zero sorrys.
-/

variable {G : Type*} [Group G]

namespace InfoGeometry.Algebra.Zorn.BruhatOrder

open List

/-! =========================================================================
    1. Words, Sublists, and Reduced Expressions
    ========================================================================= -/

/-- A word `L : List G` is composed of letters in the generating set `S`. -/
def WordOver (S : Set G) (L : List G) : Prop :=
  ∀ s ∈ L, s ∈ S

omit [Group G] in
/-- Sublists of words over `S` remain words over `S`. -/
theorem wordOver_sublist (S : Set G) {L₁ L₂ : List G}
    (hsub : L₁.Sublist L₂) (hL₂ : WordOver S L₂) :
    WordOver S L₁ := by
  intro s hs
  exact hL₂ s (hsub.subset hs)

/--
A word `L` is a reduced expression for `w = L.prod` if it has minimal length
among all words over `S` evaluating to `w`.
-/
def IsReduced (S : Set G) (L : List G) : Prop :=
  WordOver S L ∧ ∀ L' : List G, WordOver S L' → L'.prod = L.prod → L.length ≤ L'.length

/-- Equality of sublists of identical length. -/
theorem sublist_eq_of_length_eq {α : Type*} {l₁ l₂ : List α}
    (h : l₁.Sublist l₂) (hlen : l₁.length = l₂.length) : l₁ = l₂ := by
  induction h with
  | slnil => rfl
  | cons a h ih =>
    dsimp at hlen
    have := h.length_le
    omega
  | cons₂ a h ih =>
    dsimp at hlen
    congr
    exact ih (by omega)

/-! =========================================================================
    2. Bruhat Partial Order Definition
    ========================================================================= -/

/--
The strong Bruhat order `u ≤_B v`:
`u` is obtained by selecting a subword from a reduced expression of `v`.
-/
def BruhatLE (S : Set G) (u v : G) : Prop :=
  ∃ L : List G, IsReduced S L ∧ L.prod = v ∧ ∃ L' : List G, L'.Sublist L ∧ L'.prod = u

/-! =========================================================================
    3. Structural Order Properties: Reflexivity and Identity Minimality
    ========================================================================= -/

/--
THEOREM (Bruhat Reflexivity):
Every element with a reduced expression satisfies `v ≤_B v`.
-/
theorem bruhatLE_refl (S : Set G) (v : G) (h : ∃ L, IsReduced S L ∧ L.prod = v) :
    BruhatLE S v v := by
  obtain ⟨L, hred, rfl⟩ := h
  exact ⟨L, hred, rfl, L, List.Sublist.refl L, rfl⟩

/--
THEOREM (Bruhat Identity Minimality):
The identity element `1` is minimal in the Bruhat order: `1 ≤_B v` for all `v`.
-/
theorem bruhatLE_one (S : Set G) (v : G) (h : ∃ L, IsReduced S L ∧ L.prod = v) :
    BruhatLE S 1 v := by
  obtain ⟨L, hred, rfl⟩ := h
  refine ⟨L, hred, rfl, [], List.nil_sublist L, by simp⟩

/-! =========================================================================
    4. Peeling / Subword Dichotomy across Generators
    ========================================================================= -/

/-- Sublist classification on prepended words: dropping vs. keeping the head. -/
theorem sublist_cons_cases {α : Type*} (x : α) (xs : List α) (l : List α)
    (h : l.Sublist (x :: xs)) :
    l.Sublist xs ∨ ∃ l', l = x :: l' ∧ l'.Sublist xs := by
  cases h with
  | cons _ h =>
    left; exact h
  | cons₂ _ h =>
    right; exact ⟨_, rfl, h⟩

/--
THEOREM (Bruhat Subword Peeling Dichotomy):
Let `s :: L_w` be a word for `v`. Any subword evaluating to `u` either:
  1. Is a subword of `L_w` (so `u ≤_B w`), or
  2. Equals `s :: L_sub` where `L_sub.Sublist L_w` (so `s⁻¹ * u ≤_B w`).
-/
theorem bruhat_subword_cons_dichotomy (s : G) (L_w : List G)
    (u : G) (L' : List G) (hsub : L'.Sublist (s :: L_w)) (hu : L'.prod = u) :
    (∃ L_sub : List G, L_sub.Sublist L_w ∧ L_sub.prod = u) ∨
    (∃ L_sub : List G, L_sub.Sublist L_w ∧ L_sub.prod = s⁻¹ * u ∧ u = s * L_sub.prod) := by
  rcases sublist_cons_cases s L_w L' hsub with h_drop | ⟨L_tail, rfl, h_keep⟩
  · left
    exact ⟨L', h_drop, hu⟩
  · right
    have h_prod : (s :: L_tail).prod = s * L_tail.prod := List.prod_cons
    have hu_eq : u = s * L_tail.prod := hu.symm.trans h_prod
    have h_inv : L_tail.prod = s⁻¹ * u := by
      calc
        L_tail.prod = 1 * L_tail.prod := by rw [one_mul]
        _ = (s⁻¹ * s) * L_tail.prod := by rw [inv_mul_cancel]
        _ = s⁻¹ * (s * L_tail.prod) := by rw [mul_assoc]
        _ = s⁻¹ * u := by rw [← hu_eq]
    exact ⟨L_tail, h_keep, h_inv, hu_eq⟩

/-! =========================================================================
    5. Length Bounding and Antisymmetry
    ========================================================================= -/

/--
THEOREM (Bruhat Length Inequality):
If `u ≤_B v`, the length of any reduced expression for `u` is bounded by
the length of any reduced expression for `v`.
-/
theorem bruhatLE_length_le (S : Set G) (u : G) (L_u L_v : List G)
    (h_red_u : IsReduced S L_u) (h_prod_u : L_u.prod = u)
    (h_red_v : IsReduced S L_v)
    (L' : List G) (hsub : L'.Sublist L_v) (h_prod_u' : L'.prod = u) :
    L_u.length ≤ L_v.length := by
  have h_word_L' : WordOver S L' := wordOver_sublist S hsub h_red_v.1
  have h_min_u : L_u.length ≤ L'.length := by
    apply h_red_u.2 L' h_word_L'
    rw [h_prod_u, h_prod_u']
  have h_sub_len : L'.length ≤ L_v.length := hsub.length_le
  exact le_trans h_min_u h_sub_len

/--
MAIN THEOREM (Bruhat Antisymmetry):
If `u ≤_B v` and `v ≤_B u` for elements with reduced expressions, then `u = v`.
-/
theorem bruhatLE_antisymm (S : Set G) (u v : G)
    (L_u L_v : List G)
    (h_red_u : IsReduced S L_u) (h_prod_u : L_u.prod = u)
    (h_red_v : IsReduced S L_v) (h_prod_v : L_v.prod = v)
    (h_uv : ∃ L' : List G, L'.Sublist L_v ∧ L'.prod = u)
    (h_vu : ∃ L'' : List G, L''.Sublist L_u ∧ L''.prod = v) :
    u = v := by
  obtain ⟨L', hsub_uv, hprod_L'⟩ := h_uv
  obtain ⟨L'', hsub_vu, hprod_L''⟩ := h_vu
  have h_word_L' : WordOver S L' := wordOver_sublist S hsub_uv h_red_v.1
  have h_word_L'' : WordOver S L'' := wordOver_sublist S hsub_vu h_red_u.1
  have h1 : L_u.length ≤ L'.length := h_red_u.2 L' h_word_L' (hprod_L'.trans h_prod_u.symm)
  have h2 : L'.length ≤ L_v.length := hsub_uv.length_le
  have h3 : L_v.length ≤ L''.length := h_red_v.2 L'' h_word_L'' (hprod_L''.trans h_prod_v.symm)
  have h4 : L''.length ≤ L_u.length := hsub_vu.length_le
  have h_len_eq : L'.length = L_v.length := by omega
  have h_L'_eq : L' = L_v := sublist_eq_of_length_eq hsub_uv h_len_eq
  rw [← h_prod_v, ← hprod_L', h_L'_eq]

end InfoGeometry.Algebra.Zorn.BruhatOrder
