import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Data.List.Basic
import Mathlib.Data.Fin.Basic

/-!
# Inductive Peeling and Symbolic BN2 Transition on Word Lists in Lean 4

Formalizes the inductive generator peeling step for `s * wordProd L * s ∈ B ∪ B s B`
over arbitrary generator lists `L : List (Fin 6)` without finite coordinate enumeration:

  1. Complement induction: For any list `L_comp` over `Fin 6 \ {r}`,
     `s * wordProd L_comp * s ∈ B` by structural induction on `L_comp`.
  2. Simple root peeling: Prepending the simple root `r` yields
     `s * wordProd (r :: L_comp) * s ∈ B s B` via the rank-1 Levi identity.
  3. Prepending complement letters `k ≠ r` preserves `B ∪ B s B` by left absorption.
-/

variable {G : Type*} [Group G]

namespace G2InductivePeeling

/-! =========================================================================
    1. Word Products and Bruhat Cover Predicates
    ========================================================================= -/

/-- Product of group elements corresponding to an uncollected generator word `L`. -/
def wordProd (e : Fin 6 → G) (L : List (Fin 6)) : G :=
  (L.map e).prod

@[simp]
theorem wordProd_nil (e : Fin 6 → G) :
    wordProd e [] = 1 := rfl

@[simp]
theorem wordProd_cons (e : Fin 6 → G) (k : Fin 6) (L : List (Fin 6)) :
    wordProd e (k :: L) = e k * wordProd e L := rfl

/-- Membership in the big Bruhat cell `B s B`. -/
def InCellBsB (B : Subgroup G) (s x : G) : Prop :=
  ∃ b₁ ∈ B, ∃ b₂ ∈ B, x = b₁ * s * b₂

/-- Membership in the Bruhat cover `B ∪ B s B`. -/
def InBruhatCover (B : Subgroup G) (s x : G) : Prop :=
  x ∈ B ∨ InCellBsB B s x

/-- Word products over Borel generators remain in `B`. -/
theorem wordProd_mem_B (B : Subgroup G) (e : Fin 6 → G)
    (he : ∀ k, e k ∈ B) (L : List (Fin 6)) :
    wordProd e L ∈ B := by
  induction L with
  | nil => exact B.one_mem
  | cons k ks ih =>
    rw [wordProd_cons]
    exact B.mul_mem (he k) ih

/-! =========================================================================
    2. Generator Conjugation Splitting
    ========================================================================= -/

/--
LEMMA: Conjugation of a prepended word factors into the conjugate of the head
and the conjugate of the tail:
  `s * wordProd (k :: L) * s = (s * e k * s) * (s * wordProd L * s)`
-/
theorem conj_wordProd_cons (s : G) (hs : s * s = 1)
    (e : Fin 6 → G) (k : Fin 6) (L : List (Fin 6)) :
    s * wordProd e (k :: L) * s = (s * e k * s) * (s * wordProd e L * s) := by
  rw [wordProd_cons]
  have hkey : s * (e k * wordProd e L) = s * e k * wordProd e L := mul_assoc s (e k) _
  calc
    s * (e k * wordProd e L) * s
      = (s * e k * wordProd e L) * s := by rw [hkey]
    _ = (s * e k) * (wordProd e L * s) := mul_assoc _ _ _
    _ = (s * e k) * ((s * s) * (wordProd e L * s)) := by
        congr 2
        rw [hs]

/-! =========================================================================
    3. Structural Induction on Root Complement Words
    ========================================================================= -/

/--
MAIN THEOREM (Complement Word Induction):
For any word `L` composed entirely of complement roots `k ≠ r`,
the conjugate `s * wordProd L * s` lies entirely in `B`.
-/
theorem comp_word_conj_mem (B : Subgroup G) (s : G) (hs : s * s = 1)
    (e : Fin 6 → G) (r : Fin 6)
    (h_comp : ∀ k ≠ r, s * e k * s ∈ B)
    (L : List (Fin 6)) (hL : ∀ k ∈ L, k ≠ r) :
    s * wordProd e L * s ∈ B := by
  induction L with
  | nil =>
    have : s * wordProd e [] * s = 1 := by
      dsimp [wordProd]
      rw [mul_one, hs]
    rw [this]
    exact B.one_mem
  | cons k ks ih =>
    rw [conj_wordProd_cons s hs e k ks]
    have hk_ne : k ≠ r := hL k (List.Mem.head ks)
    have hks : ∀ x ∈ ks, x ≠ r := fun x hx => hL x (List.Mem.tail k hx)
    have hk_mem : s * e k * s ∈ B := h_comp k hk_ne
    have hks_mem : s * wordProd e ks * s ∈ B := ih hks
    exact B.mul_mem hk_mem hks_mem

/-! =========================================================================
    4. Inductive Peeling Steps: Simple Root vs. Complement Letter
    ========================================================================= -/

/--
THEOREM (Peeling Step - Simple Root Head):
Prepending the active simple root `r` to a complement word `L` moves the
conjugate into the big cell `B s B`.
-/
theorem peeling_step_simple (B : Subgroup G) (s : G) (hs : s * s = 1)
    (e : Fin 6 → G) (he : ∀ k, e k ∈ B) (r : Fin 6)
    (h_levi : s * e r * s = e r * s * e r)
    (h_comp : ∀ k ≠ r, s * e k * s ∈ B)
    (L : List (Fin 6)) (hL : ∀ k ∈ L, k ≠ r) :
    InBruhatCover B s (s * wordProd e (r :: L) * s) := by
  right
  rw [conj_wordProd_cons s hs e r L]
  rw [h_levi]
  have h_rest : s * wordProd e L * s ∈ B := comp_word_conj_mem B s hs e r h_comp L hL
  have h_b1 : e r ∈ B := he r
  have h_b2 : e r * (s * wordProd e L * s) ∈ B := B.mul_mem (he r) h_rest
  refine ⟨e r, h_b1, e r * (s * wordProd e L * s), h_b2, ?_⟩
  calc
    (e r * s * e r) * (s * wordProd e L * s)
      = e r * s * (e r * (s * wordProd e L * s)) := by
        simp only [mul_assoc]

/--
THEOREM (Peeling Step - Complement Letter Head):
Prepending any complement root `k ≠ r` preserves membership in `B ∪ B s B`
by left multiplication by `s * e k * s ∈ B`.
-/
theorem peeling_step_complement (B : Subgroup G) (s : G) (hs : s * s = 1)
    (e : Fin 6 → G) (r : Fin 6)
    (h_comp : ∀ k ≠ r, s * e k * s ∈ B)
    (k : Fin 6) (hk : k ≠ r)
    (L : List (Fin 6))
    (h_cover : InBruhatCover B s (s * wordProd e L * s)) :
    InBruhatCover B s (s * wordProd e (k :: L) * s) := by
  rw [conj_wordProd_cons s hs e k L]
  have hk_mem : s * e k * s ∈ B := h_comp k hk
  rcases h_cover with hB | ⟨b₁, hb₁, b₂, hb₂, h_eq⟩
  · left
    exact B.mul_mem hk_mem hB
  · right
    refine ⟨(s * e k * s) * b₁, B.mul_mem hk_mem hb₁, b₂, hb₂, ?_⟩
    rw [h_eq]
    simp only [mul_assoc]

/-! =========================================================================
    5. Main Factorized BN2 Theorem
    ========================================================================= -/

/--
MAIN THEOREM (Factorized Word BN2 Coverage):
Any unipotent word factorized into an optional simple root generator `r`
followed by a complement word `L_comp` satisfies `s * wordProd L * s ∈ B ∪ B s B`.
-/
theorem peeling_factorized_bn2 (B : Subgroup G) (s : G) (hs : s * s = 1)
    (e : Fin 6 → G) (he : ∀ k, e k ∈ B) (r : Fin 6)
    (h_levi : s * e r * s = e r * s * e r)
    (h_comp : ∀ k ≠ r, s * e k * s ∈ B)
    (has_simple : Bool) (L_comp : List (Fin 6)) (h_comp_word : ∀ k ∈ L_comp, k ≠ r) :
    InBruhatCover B s (s * wordProd e ((if has_simple then [r] else []) ++ L_comp) * s) := by
  cases has_simple
  · simp only [Bool.false_eq_true, ↓reduceIte, List.nil_append]
    left
    exact comp_word_conj_mem B s hs e r h_comp L_comp h_comp_word
  · simp only [↓reduceIte, List.singleton_append]
    exact peeling_step_simple B s hs e he r h_levi h_comp L_comp h_comp_word

end G2InductivePeeling
