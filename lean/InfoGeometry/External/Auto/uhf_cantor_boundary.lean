import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.CategoryTheory.Functor.OfSequence
import Mathlib.CategoryTheory.Limits.HasLimits
import Mathlib.CategoryTheory.Limits.Filtered
import Mathlib.CategoryTheory.Limits.Types.Filtered

open CategoryTheory
open CategoryTheory.Limits

namespace UHFCantorBoundary

/-!
  UHF bulk (finite diagonal stages) → Cantor boundary, with MASA correction.
  The point is: the boundary is from the diagonal MASA, not from the full UHF spectrum.
-/

/-- Finite diagonal level at stage n: binary words of length n. -/
def DiagonalLevel (n : ℕ) : Type := Fin n → Bool

/-- Embedding `D_n ↪ D_{n+1}` by appending a fixed `false` bit. -/
def diagonalEmbed (n : ℕ) : DiagonalLevel n → DiagonalLevel (n + 1) :=
  fun b i => if h : i.1 < n then b ⟨i.1, h⟩ else false

lemma diagonalEmbed_lt (n : ℕ) (b : DiagonalLevel n) {k : ℕ} (hk : k < n) :
    diagonalEmbed n b ⟨k, Nat.lt_succ_of_lt hk⟩ = b ⟨k, hk⟩ := by
  simp [diagonalEmbed, hk]

lemma diagonalEmbed_eq (n : ℕ) (b : DiagonalLevel n) :
    diagonalEmbed n b ⟨n, Nat.lt_succ_self n⟩ = false := by
  simp [diagonalEmbed]

/-- The finite diagonal diagram as a functor `ℕ ⥤ Type`: `D_n → D_{n+1}`. -/
def diagonalDiagram : ℕ ⥤ Type := Functor.ofSequence diagonalEmbed

/-- The `2`-adic/UHF-bulk colimit over diagonal finite levels (as a type-level colimit). -/
def uHFColimit : Type := colimit diagonalDiagram

/-- Infinite binary strings: `CantorBoundary = {0,1}^ℕ`. -/
def CantorBoundary : Type := ℕ → Bool

/-- Finite-to-infinite readout (zero padding beyond stage). -/
def finiteToBoundary (n : ℕ) : DiagonalLevel n → CantorBoundary :=
  fun b k => if h : k < n then b ⟨k, h⟩ else false

/-- Cocone from finite levels into `CantorBoundary`. -/
def boundaryCocone : Cocone diagonalDiagram where
  pt := CantorBoundary
  ι := NatTrans.ofSequence
    (app := finiteToBoundary)
    (naturality := by
      intro n
      funext b k
      have hmap : diagonalDiagram.map (homOfLE (Nat.le_add_right n 1)) = diagonalEmbed n := by
        simp [diagonalDiagram, Functor.ofSequence_map_homOfLE_succ]
      rw [hmap]
      by_cases hkn : k < n
      · have hk1 : k < n + 1 := Nat.lt_succ_of_lt hkn
        simp [finiteToBoundary, hkn, hk1, diagonalEmbed_lt n b hkn]
      · by_cases hk : k < n + 1
        · have hk' : k = n := Nat.eq_of_lt_succ_of_not_lt hk hkn
          subst hk'
          simp [finiteToBoundary, diagonalEmbed_eq]
        · simp [finiteToBoundary, hkn, hk])

/-- Map from the colimit to the Cantor boundary (projective readout). -/
noncomputable def fromColimitBoundary : colimit diagonalDiagram → CantorBoundary :=
  colimit.desc (F := diagonalDiagram) (c := boundaryCocone)

/-- Canonical identification of the boundary type. -/
def cantor_boundary_identification : CantorBoundary ≃ (ℕ → Bool) :=
  Equiv.refl _

/-- Correction statement (for comments/theory):
`Spec(UHF_{2^∞})` is not used here;
`Spec(D_{2^∞})` (diagonal MASA) is realized as CantorBoundary. -/
def cantor_is_diagonal_spectrum : CantorBoundary ≃ (ℕ → Bool) :=
  cantor_boundary_identification

/-- General Zorn pattern (nonempty chain hypothesis ⇒ maximal extension). -/
theorem zorn_refinement_exists
    {S : Set (Set ℕ)}
    (h : ∀ c ⊆ S, IsChain (· ⊆ ·) c → c.Nonempty →
      ∃ ub ∈ S, ∀ s ∈ c, s ⊆ ub) (x : Set ℕ) (hx : x ∈ S) :
    ∃ M, x ⊆ M ∧ Maximal (· ∈ S) M :=
  zorn_subset_nonempty S h x hx

/-- Category formulation reminder:
A preorder is a thin category (`SmallCategory`) in which homs encode ≤. -/
def diagonal_prefix_category (C : Type*) [Preorder C] : SmallCategory C :=
  (inferInstance : SmallCategory C)

end UHFCantorBoundary
