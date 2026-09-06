import Mathlib.Analysis.Convex.Radon

/-!
# Radon and Helly Theorems

Mathlib-native bridge for Radon and Helly results, re-exported in the
`InfoGeometry.Convex` namespace.
-/

namespace InfoGeometry.Convex

open Fintype Finset Set
open Module

variable {ι 𝕜 E : Type*}
variable [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable [AddCommGroup E] [Module 𝕜 E]

/-- Radon's theorem on convex sets, re-exported from Mathlib. -/
theorem radon_partition {f : ι → E} (h : ¬ AffineIndependent 𝕜 f) :
    ∃ I, (convexHull 𝕜 (f '' I) ∩ convexHull 𝕜 (f '' Iᶜ)).Nonempty :=
  _root_.Convex.radon_partition (f := f) h

section FiniteDimensional

variable [FiniteDimensional 𝕜 E]

/-- Helly's theorem for finite indexed families (cardinality `≤ d + 1` form). -/
theorem helly_theorem' {F : ι → Set E} {s : Finset ι}
    (h_convex : ∀ i ∈ s, Convex 𝕜 (F i))
    (h_inter : ∀ I ⊆ s, #I ≤ finrank 𝕜 E + 1 → (⋂ i ∈ I, F i).Nonempty) :
    (⋂ i ∈ s, F i).Nonempty :=
  _root_.Convex.helly_theorem' (h_convex := h_convex) (h_inter := h_inter)

/-- Helly's theorem for finite indexed families (classical `= d + 1` form). -/
theorem helly_theorem {F : ι → Set E} {s : Finset ι}
    (h_card : finrank 𝕜 E + 1 ≤ #s)
    (h_convex : ∀ i ∈ s, Convex 𝕜 (F i))
    (h_inter : ∀ I ⊆ s, #I = finrank 𝕜 E + 1 → (⋂ i ∈ I, F i).Nonempty) :
    (⋂ i ∈ s, F i).Nonempty :=
  _root_.Convex.helly_theorem
    (h_card := h_card) (h_convex := h_convex) (h_inter := h_inter)

/-- Helly's theorem for finite sets of convex sets (`≤ d + 1` form). -/
theorem helly_theorem_set' {F : Finset (Set E)}
    (h_convex : ∀ X ∈ F, Convex 𝕜 X)
    (h_inter : ∀ G : Finset (Set E), G ⊆ F → #G ≤ finrank 𝕜 E + 1 →
      (⋂₀ (G : Set (Set E))).Nonempty) :
    (⋂₀ (F : Set (Set E))).Nonempty :=
  _root_.Convex.helly_theorem_set' (h_convex := h_convex) (h_inter := h_inter)

/-- Helly's theorem for finite sets of convex sets (classical `= d + 1` form). -/
theorem helly_theorem_set {F : Finset (Set E)}
    (h_card : finrank 𝕜 E + 1 ≤ #F)
    (h_convex : ∀ X ∈ F, Convex 𝕜 X)
    (h_inter : ∀ G : Finset (Set E), G ⊆ F → #G = finrank 𝕜 E + 1 →
      (⋂₀ (G : Set (Set E))).Nonempty) :
    (⋂₀ (F : Set (Set E))).Nonempty :=
  _root_.Convex.helly_theorem_set
    (h_card := h_card) (h_convex := h_convex) (h_inter := h_inter)

section Compact

variable [TopologicalSpace E] [T2Space E]

/-- Helly's theorem for compact convex indexed families (`≤ d + 1` form). -/
theorem helly_theorem_compact' {F : ι → Set E}
    (h_convex : ∀ i, Convex 𝕜 (F i))
    (h_compact : ∀ i, IsCompact (F i))
    (h_inter : ∀ I : Finset ι, #I ≤ finrank 𝕜 E + 1 → (⋂ i ∈ I, F i).Nonempty) :
    (⋂ i, F i).Nonempty :=
  _root_.Convex.helly_theorem_compact'
    (h_convex := h_convex) (h_compact := h_compact) (h_inter := h_inter)

/-- Helly's theorem for compact convex indexed families (classical `= d + 1` form). -/
theorem helly_theorem_compact {F : ι → Set E}
    (h_card : finrank 𝕜 E + 1 ≤ ENat.card ι)
    (h_convex : ∀ i, Convex 𝕜 (F i))
    (h_compact : ∀ i, IsCompact (F i))
    (h_inter : ∀ I : Finset ι, #I = finrank 𝕜 E + 1 → (⋂ i ∈ I, F i).Nonempty) :
    (⋂ i, F i).Nonempty :=
  _root_.Convex.helly_theorem_compact
    (h_card := h_card) (h_convex := h_convex) (h_compact := h_compact) (h_inter := h_inter)

/-- Helly's theorem for compact convex sets (`≤ d + 1` form). -/
theorem helly_theorem_set_compact' {F : Set (Set E)}
    (h_convex : ∀ X ∈ F, Convex 𝕜 X)
    (h_compact : ∀ X ∈ F, IsCompact X)
    (h_inter : ∀ G : Finset (Set E), (G : Set (Set E)) ⊆ F → #G ≤ finrank 𝕜 E + 1 →
      (⋂₀ (G : Set (Set E))).Nonempty) :
    (⋂₀ (F : Set (Set E))).Nonempty :=
  _root_.Convex.helly_theorem_set_compact'
    (h_convex := h_convex) (h_compact := h_compact) (h_inter := h_inter)

/-- Helly's theorem for compact convex sets (classical `= d + 1` form). -/
theorem helly_theorem_set_compact {F : Set (Set E)}
    (h_card : finrank 𝕜 E + 1 ≤ F.encard)
    (h_convex : ∀ X ∈ F, Convex 𝕜 X)
    (h_compact : ∀ X ∈ F, IsCompact X)
    (h_inter : ∀ G : Finset (Set E), (G : Set (Set E)) ⊆ F → #G = finrank 𝕜 E + 1 →
      (⋂₀ (G : Set (Set E))).Nonempty) :
    (⋂₀ (F : Set (Set E))).Nonempty :=
  _root_.Convex.helly_theorem_set_compact
    (h_card := h_card) (h_convex := h_convex) (h_compact := h_compact) (h_inter := h_inter)

end Compact
end FiniteDimensional
end InfoGeometry.Convex
