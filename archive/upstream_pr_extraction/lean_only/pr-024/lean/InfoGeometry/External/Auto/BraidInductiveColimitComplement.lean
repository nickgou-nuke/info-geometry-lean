import Mathlib

/-!
# Braid Inductive-Colimit Complement

This module complements `external_refs/braids_better` without depending on its
heavier files.  It records the local generator-index skeleton:

* finite braid stages have generators `Fin n`;
* the successor inclusion is `castSucc`;
* every finite generator embeds into the infinite generator boundary `ℕ`;
* adjacent and separated Artin pairs are stable under the finite-to-infinite
  embedding.

This is an induction/colimit compatibility lane for finite generator indices.
It does not construct a categorical colimit of braid groups and does not prove
injectivity of the monoid-to-group map.
-/

noncomputable section

namespace BraidInductiveColimitComplement

/-- Stage-`n` braid generators. -/
abbrev FiniteBraidGenerators (n : ℕ) : Type :=
  Fin n

/-- Infinite braid-generator boundary. -/
abbrev InfiniteBraidGenerators : Type :=
  ℕ

/-- Successor inclusion of finite braid generators. -/
def finiteSuccEmbed (n : ℕ) : FiniteBraidGenerators n → FiniteBraidGenerators (n + 1) :=
  Fin.castSucc

/-- Inclusion of a finite stage into the infinite braid-generator boundary. -/
def finiteToInfinite {n : ℕ} (i : FiniteBraidGenerators n) : InfiniteBraidGenerators :=
  i.1

theorem finiteSuccEmbed_val (n : ℕ) (i : FiniteBraidGenerators n) :
    (finiteSuccEmbed n i).1 = i.1 := by
  rfl

theorem finiteToInfinite_succ_compatible
    (n : ℕ) (i : FiniteBraidGenerators n) :
    finiteToInfinite (finiteSuccEmbed n i) = finiteToInfinite i := by
  rfl

theorem finiteToInfinite_injective (n : ℕ) :
    Function.Injective (@finiteToInfinite n) := by
  intro i j h
  exact Fin.ext h

theorem finite_stage_card (n : ℕ) :
    Fintype.card (FiniteBraidGenerators n) = n := by
  simp [FiniteBraidGenerators]

/-- Adjacent finite generators, the source of `σᵢ σᵢ₊₁ σᵢ = σᵢ₊₁ σᵢ σᵢ₊₁`. -/
def finiteAdjacent {n : ℕ} (i j : FiniteBraidGenerators n) : Prop :=
  i.1 + 1 = j.1

/-- Separated finite generators, the source of `σᵢ σⱼ = σⱼ σᵢ`. -/
def finiteSeparated {n : ℕ} (i j : FiniteBraidGenerators n) : Prop :=
  i.1 + 2 ≤ j.1 ∨ j.1 + 2 ≤ i.1

/-- Infinite adjacent generator relation predicate. -/
def infiniteAdjacent (i j : InfiniteBraidGenerators) : Prop :=
  i + 1 = j

/-- Infinite separated generator relation predicate. -/
def infiniteSeparated (i j : InfiniteBraidGenerators) : Prop :=
  i + 2 ≤ j ∨ j + 2 ≤ i

theorem adjacent_embeds_to_infinite
    {n : ℕ} {i j : FiniteBraidGenerators n}
    (h : finiteAdjacent i j) :
    infiniteAdjacent (finiteToInfinite i) (finiteToInfinite j) := by
  exact h

theorem separated_embeds_to_infinite
    {n : ℕ} {i j : FiniteBraidGenerators n}
    (h : finiteSeparated i j) :
    infiniteSeparated (finiteToInfinite i) (finiteToInfinite j) := by
  exact h

theorem adjacent_stable_under_succ
    {n : ℕ} {i j : FiniteBraidGenerators n}
    (h : finiteAdjacent i j) :
    finiteAdjacent (finiteSuccEmbed n i) (finiteSuccEmbed n j) := by
  exact h

theorem separated_stable_under_succ
    {n : ℕ} {i j : FiniteBraidGenerators n}
    (h : finiteSeparated i j) :
    finiteSeparated (finiteSuccEmbed n i) (finiteSuccEmbed n j) := by
  exact h

/-- A finite braid word as a list of finite-stage generator indices. -/
abbrev FiniteBraidWord (n : ℕ) : Type :=
  List (FiniteBraidGenerators n)

/-- Boundary image of a finite braid word. -/
def wordToInfinite {n : ℕ} (w : FiniteBraidWord n) : List InfiniteBraidGenerators :=
  w.map finiteToInfinite

/-- Successor embedding of a finite braid word. -/
def wordSuccEmbed {n : ℕ} (w : FiniteBraidWord n) : FiniteBraidWord (n + 1) :=
  w.map (finiteSuccEmbed n)

theorem wordToInfinite_succ_compatible
    {n : ℕ} (w : FiniteBraidWord n) :
    wordToInfinite (wordSuccEmbed w) = wordToInfinite w := by
  induction w with
  | nil =>
      rfl
  | cons i rest ih =>
      simp [wordToInfinite, wordSuccEmbed, finiteToInfinite_succ_compatible]

theorem wordToInfinite_length {n : ℕ} (w : FiniteBraidWord n) :
    (wordToInfinite w).length = w.length := by
  simp [wordToInfinite]

theorem wordSuccEmbed_length {n : ℕ} (w : FiniteBraidWord n) :
    (wordSuccEmbed w).length = w.length := by
  simp [wordSuccEmbed]

/--
Consolidated complement: the finite braid-generator tower has a stable
infinite boundary, and adjacent/separated Artin relation indices are preserved.
-/
theorem braid_inductive_colimit_complement_synthesis :
    (∀ n : ℕ, Fintype.card (FiniteBraidGenerators n) = n) ∧
    (∀ n : ℕ, Function.Injective (@finiteToInfinite n)) ∧
    (∀ n : ℕ, ∀ i : FiniteBraidGenerators n,
      finiteToInfinite (finiteSuccEmbed n i) = finiteToInfinite i) ∧
    (∀ n : ℕ, ∀ i j : FiniteBraidGenerators n,
      finiteAdjacent i j →
        infiniteAdjacent (finiteToInfinite i) (finiteToInfinite j)) ∧
    (∀ n : ℕ, ∀ i j : FiniteBraidGenerators n,
      finiteSeparated i j →
        infiniteSeparated (finiteToInfinite i) (finiteToInfinite j)) ∧
    (∀ n : ℕ, ∀ w : FiniteBraidWord n,
      wordToInfinite (wordSuccEmbed w) = wordToInfinite w) ∧
    (∀ n : ℕ, ∀ w : FiniteBraidWord n,
      (wordToInfinite w).length = w.length) := by
  exact ⟨finite_stage_card,
    finiteToInfinite_injective,
    finiteToInfinite_succ_compatible,
    fun _ _ _ h => adjacent_embeds_to_infinite h,
    fun _ _ _ h => separated_embeds_to_infinite h,
    fun _ w => wordToInfinite_succ_compatible w,
    fun _ w => wordToInfinite_length w⟩

end BraidInductiveColimitComplement

end noncomputable section
