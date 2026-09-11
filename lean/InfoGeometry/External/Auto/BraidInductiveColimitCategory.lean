import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.CategoryTheory.Functor.OfSequence
import Mathlib.CategoryTheory.Limits.HasLimits
import Mathlib.CategoryTheory.Limits.Filtered
import Mathlib.CategoryTheory.Limits.Types.Filtered
import InfoGeometry.External.Auto.BraidInductiveColimitComplement

/-!
# Categorical colimit package for the braid finite-index tower

This file upgrades the finite-to-infinite index compatibility of
`BraidInductiveColimitComplement` to explicit category-theoretic cocones over the
`ℕ`-diagram `n ↦ Fin n` and the induced diagram on finite braid words.
-/

noncomputable section

namespace BraidInductiveColimitComplement

open CategoryTheory
open CategoryTheory.Limits

/-- The index-`n` generator diagram `Fin n` with successor maps `castSucc`. -/
def braidGeneratorDiagram : ℕ ⥤ Type _ :=
  Functor.ofSequence finiteSuccEmbed

/-- The categorical colimit of the finite generator stages. -/
def braidGeneratorColimit : Type _ :=
  colimit braidGeneratorDiagram

/-- Boundary cocone from finite stages into `ℕ`. -/
def braidGeneratorBoundaryCocone : Cocone braidGeneratorDiagram where
  pt := InfiniteBraidGenerators
  ι :=
    NatTrans.ofSequence
      (app := fun n => finiteToInfinite)
      (naturality := by
        intro n
        funext i
        have hmap : braidGeneratorDiagram.map (homOfLE (Nat.le_succ n)) = finiteSuccEmbed n := by
          simpa [braidGeneratorDiagram] using
            (Functor.ofSequence_map_homOfLE_succ (f := finiteSuccEmbed) n)
        simp [hmap, finiteToInfinite_succ_compatible])

/-- The induced boundary map out of the colimit of generator stages. -/
def generatorFromColimit : braidGeneratorColimit → InfiniteBraidGenerators :=
  colimit.desc (F := braidGeneratorDiagram) (c := braidGeneratorBoundaryCocone)

/-- On each stage this agrees with the finite inclusion. -/
theorem generatorFromColimit_ι (n : ℕ) (i : FiniteBraidGenerators n) :
    generatorFromColimit (colimit.ι braidGeneratorDiagram n i) = finiteToInfinite i := by
  simp [generatorFromColimit, braidGeneratorBoundaryCocone]

/-- Words over finite generators at stage `n`. -/
def braidWordDiagram : ℕ ⥤ Type _ :=
  Functor.ofSequence (fun n => wordSuccEmbed (n := n))

/-- The categorical colimit of finite generator words (at increasing stage). -/
def braidWordColimit : Type _ :=
  colimit braidWordDiagram

/-- The boundary cocone from finite-stage words to infinite words. -/
def braidWordBoundaryCocone : Cocone braidWordDiagram where
  pt := List InfiniteBraidGenerators
  ι :=
    NatTrans.ofSequence
      (app := fun n => wordToInfinite (n := n))
      (naturality := by
        intro n
        funext w
        have hmap : braidWordDiagram.map (homOfLE (Nat.le_succ n)) = wordSuccEmbed (n := n) := by
          simpa [braidWordDiagram] using
            (Functor.ofSequence_map_homOfLE_succ (f := fun n => wordSuccEmbed (n := n)) n)
        simp [hmap, wordToInfinite_succ_compatible])

/-- The induced boundary word map out of the colimit of words. -/
def wordFromColimit : braidWordColimit → List InfiniteBraidGenerators :=
  colimit.desc (F := braidWordDiagram) (c := braidWordBoundaryCocone)

/-- On words, colimit inclusion agrees with `wordToInfinite`. -/
theorem wordFromColimit_ι (n : ℕ) (w : FiniteBraidWord n) :
    wordFromColimit (colimit.ι braidWordDiagram n w) = wordToInfinite w := by
  simp [wordFromColimit, braidWordBoundaryCocone]

/-- Finite-stage boundary words preserve length. -/
theorem wordBoundary_length (n : ℕ) (w : FiniteBraidWord n) :
    (wordFromColimit (colimit.ι braidWordDiagram n w)).length = w.length := by
  rw [wordFromColimit_ι]
  exact wordToInfinite_length (n := n) w

/-- Auxiliary map-level injectivity: injective letter map gives injective list map. -/
theorem listMap_injective {α β : Type*} {f : α → β}
    (hf : Function.Injective f) : Function.Injective (List.map f) := by
  intro l₁ l₂ h
  induction l₁ generalizing l₂ with
  | nil =>
      cases l₂ with
      | nil => rfl
      | cons _ _ =>
          simp at h
  | cons a as ih =>
      cases l₂ with
      | nil =>
          simp at h
      | cons b bs =>
          have hsplit : f a = f b ∧ List.map f as = List.map f bs := by
            simpa [List.map] using h
          have hab : a = b := hf hsplit.1
          cases hab
          have htail : as = bs := ih hsplit.2
          cases htail
          rfl

/-- For each fixed stage, finite braid-word boundary map is injective. -/
theorem wordToInfinite_injective (n : ℕ) :
    Function.Injective (wordToInfinite : FiniteBraidWord n → List InfiniteBraidGenerators) :=
  listMap_injective (finiteToInfinite_injective n)

/-- Compact theorem package: the finite-to-infinite compatibility lemmas assemble into
an honest categorical colimit model of the index tower. -/
theorem braid_inductive_colimit_category_synthesis :
    (∀ n i, generatorFromColimit (colimit.ι braidGeneratorDiagram n i) = finiteToInfinite i) ∧
    (∀ n w, wordFromColimit (colimit.ι braidWordDiagram n w) = wordToInfinite w) := by
  exact ⟨generatorFromColimit_ι, wordFromColimit_ι⟩

end BraidInductiveColimitComplement

end noncomputable section
