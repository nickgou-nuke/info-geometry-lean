/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Empty
import Mathlib.Data.Finset.Filter
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Sym.Basic
import Mathlib.Tactic

/-!
# MHV triplet/doublet combinatorics

Combinatorial core of arXiv:2512.25005
("Grassmannian Geometries for Non-Planar On-Shell Diagrams",
Lisitsyn–Oktem–Sherman-Bennett–Trnka).

An MHV leading-singularity diagram on `n` external legs is encoded by `n − 2`
triplets (3-subsets of `[n]`). This file formalizes the triplet/doublet substrate
of the paper:

- `isTriplet` : a 3-element subset of `α`
- `pairCount` : number of triplets containing an unordered pair (`p : Sym2 α`),
  defined via `Sym2.lift` so it is independent of the chosen representative
- `doublets` : unordered pairs occurring in an odd number of triplets (Eq. 4.8)
- `nonVanishing` : Lemma 1 / Eq. 4.4, every nonempty subset of `d` triplets
  touches at least `d + 2` indices
- `validSubset` : a subset using `d` triplets on exactly `d + 2` indices
  (the setup of Lemma 2 / Eq. 4.5)

The full sphere-move equivalence (Theorem 3) and the Grassmannian geometry
(Section 5) are the relational mechanics to be layered on this substrate.
-/

namespace InfoGeometry.Combinatorics.MHVTriplets

universe u

variable {α : Type*}
variable [Fintype α] [DecidableEq α]

/-- A triplet is a 3-element subset of `α` (one black vertex of an MHV diagram). -/
def isTriplet (t : Finset α) : Prop := t.card = 3

def pairCountAux (T : Finset (Finset α)) (i j : α) : ℕ :=
  (T.filter (fun t => i ∈ t ∧ j ∈ t)).card

def pairCountAux_symm (T : Finset (Finset α)) : ∀ (a b : α), pairCountAux T a b = pairCountAux T b a := by
  intro a b
  have h₂ : T.filter (fun t => a ∈ t ∧ b ∈ t) = T.filter (fun t => b ∈ t ∧ a ∈ t) := by
    apply Finset.ext
    intro x
    constructor <;> intro h
    · simp [Finset.mem_filter] at h ⊢
      exact ⟨h.1, ⟨h.2.2, h.2.1⟩⟩
    · simp [Finset.mem_filter] at h ⊢
      exact ⟨h.1, ⟨h.2.2, h.2.1⟩⟩
  rw [pairCountAux, pairCountAux, h₂]
  <;> rfl

/-- Number of triplets in `T` containing both elements of the unordered pair `p : Sym2 α`.
Defined via `Sym2.lift`, hence independent of the chosen representative of `p`. -/
def pairCount (T : Finset (Finset α)) : Sym2 α → ℕ :=
  Sym2.lift (⟨pairCountAux T, pairCountAux_symm T⟩ : {f : α → α → ℕ // ∀ (a₁ a₂ : α), f a₁ a₂ = f a₂ a₁})

theorem pairCount_mk (T : Finset (Finset α)) (i j : α) :
    pairCount T (Sym2.mk i j) = pairCountAux T i j := by
  unfold pairCount
  <;> simp [Sym2.lift_mk]
  <;> rfl

theorem pairCount_sym (T : Finset (Finset α)) (i j : α) :
    pairCount T (Sym2.mk i j) = pairCount T (Sym2.mk j i) := by
  calc
    pairCount T (Sym2.mk i j) = pairCountAux T i j := by rw [pairCount_mk]
    _ = pairCountAux T j i := by rw [pairCountAux_symm]
    _ = pairCount T (Sym2.mk j i) := by rw [pairCount_mk]

theorem pairCount_empty (p : Sym2 α) : pairCount (∅ : Finset (Finset α)) p = 0 := by
  have h : ∀ (i j : α), pairCount (∅ : Finset (Finset α)) (Sym2.mk i j) = 0 := by
    intro i j
    have h₁ : pairCount (∅ : Finset (Finset α)) (Sym2.mk i j) = pairCountAux (∅ : Finset (Finset α)) i j := by
      rw [pairCount_mk]
    rw [h₁]
    unfold pairCountAux
    simp [Finset.filter_empty]
    <;> aesop
  -- Every unordered pair is `Sym2.mk i j` for some `i j`.
  have h₂ : pairCount (∅ : Finset (Finset α)) p = 0 := by
    have h₃ := @Sym2.inductionOn α (fun q => pairCount (∅ : Finset (Finset α)) q = 0) p h
    exact h₃
  exact h₂

/-- Doublets of `T`: unordered pairs occurring in an odd number of triplets (Eq. 4.8). -/
def doublets (T : Finset (Finset α)) : Finset (Sym2 α) :=
  (Finset.univ : Finset (Sym2 α)).filter (fun p => (pairCount T p % 2 = 1))

theorem doublets_mem_iff (T : Finset (Finset α)) (p : Sym2 α) :
    p ∈ doublets T ↔ pairCount T p % 2 = 1 := by
  simp [doublets, Finset.mem_filter]

theorem doublets_empty : doublets (∅ : Finset (Finset α)) = ∅ := by
  apply Finset.ext
  intro p
  simp [doublets, Finset.mem_filter, pairCount_empty, Set.mem_empty_iff_false]
  <;> tauto

/-- Pair-count is bounded by the number of triplets. -/
theorem pairCount_le_cardT (T : Finset (Finset α)) (p : Sym2 α) :
    pairCount T p ≤ T.card := by
  have h : ∀ (i j : α), pairCount T (Sym2.mk i j) ≤ T.card := by
    intro i j
    have h₁ : pairCount T (Sym2.mk i j) = pairCountAux T i j := by rw [pairCount_mk]
    rw [h₁]
    dsimp [pairCountAux]
    have h₂ : (T.filter (fun t => i ∈ t ∧ j ∈ t)) ⊆ T := by
      apply Finset.filter_subset
    exact Finset.card_le_card h₂
  -- Lift the bound from representatives `Sym2.mk i j` to an arbitrary `p : Sym2 α`.
  have h₂ : pairCount T p ≤ T.card := by
    have h₃ := @Sym2.inductionOn α (fun q : Sym2 α => pairCount T q ≤ T.card) p (fun x y => h x y)
    exact h₃
  exact h₂

/-- Non-vanishing condition (Lemma 1 / Eq. 4.4): every nonempty subset of `d`
triplets touches at least `d + 2` indices.  The empty subset is excluded because
it imposes no rank constraint on `C⊥` (it has no rows), consistent with the
paper's rank-deficiency argument. -/
def nonVanishing (T : Finset (Finset α)) : Prop :=
  ∀ (S : Finset (Finset α)), S ⊆ T → S ≠ ∅ → (S.biUnion id).card ≥ S.card + 2

theorem nonVanishing_empty : nonVanishing (∅ : Finset (Finset α)) := by
  intro S hS hne
  have h₁ : S = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro x hx
    have h₂ : x ∈ S := hx
    have h₃ : x ∈ ∅ := hS h₂
    simp [Set.mem_empty_iff_false] at h₃
    <;> tauto
  have h₂ : False := hne h₁
  exfalso
  exact h₂

theorem nonVanishing_mono {T₁ T₂ : Finset (Finset α)} (h : T₁ ⊆ T₂) (h₂ : nonVanishing T₂) :
    nonVanishing T₁ := by
  intro S hS hne
  have hS' : S ⊆ T₂ := hS.trans h
  have h₃ : (S.biUnion id).card ≥ S.card + 2 := h₂ S hS' hne
  exact h₃

/-- A valid subset `R` of `T` uses `d` triplets on exactly `d + 2` indices
(with `n = Fintype.card α`), the setup of Lemma 2 / Eq. 4.5. -/
def validSubset (n : ℕ) (T : Finset (Finset α)) (R : Finset (Finset α)) : Prop :=
  R ⊆ T ∧ R.card + 2 ≤ n ∧ (R.biUnion id).card = R.card + 2
