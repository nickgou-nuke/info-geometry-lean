import proofs.KleinGlideCovering
import Mathlib.Topology.VectorBundle.Basic

/-!
# A chosen covering atlas for the Klein glide quotient

This owner extracts, at every point of the literal orbit quotient, a lift and
one of the disjoint sheet neighbourhoods supplied by
`IsAddQuotientCoveringMap`.  The resulting trivializations are the input for
the associated six-state `VectorBundleCore`.
-/

noncomputable section
namespace KleinGlideCoveringAtlas

open Topology
open KleinBrillouinBase KleinBottleOrbitQuotient KleinGlideCovering

abbrev Base := KleinBrillouinQuotient
abbrev Cover := BrillouinTorus

/-- A chosen point in the covering torus above `b`. -/
def liftAt (b : Base) : Cover := Function.surjInv quotientMap_surjective b

@[simp] theorem quotientMap_liftAt (b : Base) : quotientMap (liftAt b) = b :=
  Function.surjInv_eq quotientMap_surjective b

/-- A neighbourhood of the chosen lift whose two deck translates are
disjoint. -/
def rawSheetSet (b : Base) : Set Cover :=
  Classical.choose (quotientMap_isAddQuotientCovering.disjoint (liftAt b))

theorem rawSheetSet_mem_nhds (b : Base) : rawSheetSet b ∈ nhds (liftAt b) :=
  (Classical.choose_spec
    (quotientMap_isAddQuotientCovering.disjoint (liftAt b))).1

theorem rawSheetSet_disjoint (b : Base) (g : Deck2)
    (h : (((g +ᵥ ·) '' rawSheetSet b) ∩ rawSheetSet b).Nonempty) : g = 0 :=
  (Classical.choose_spec
    (quotientMap_isAddQuotientCovering.disjoint (liftAt b))).2 g h

/-- The open sheet used for the chart at `b`. -/
def sheetSet (b : Base) : Set Cover := interior (rawSheetSet b)

theorem isOpen_sheetSet (b : Base) : IsOpen (sheetSet b) := isOpen_interior

theorem liftAt_mem_sheetSet (b : Base) : liftAt b ∈ sheetSet b :=
  mem_interior_iff_mem_nhds.mpr (rawSheetSet_mem_nhds b)

theorem sheetSet_disjoint (b : Base) (g : Deck2)
    (h : (((g +ᵥ ·) '' sheetSet b) ∩ sheetSet b).Nonempty) : g = 0 :=
  rawSheetSet_disjoint b g (h.mono (by
    intro x hx
    rcases hx with ⟨⟨y, hy, rfl⟩, hx⟩
    exact ⟨⟨y, interior_subset hy, rfl⟩, interior_subset hx⟩))

/-- The covering trivialization chosen at each base point. -/
def coverTriv (b : Base) : Trivialization Deck2 quotientMap :=
  quotientMap_isAddQuotientCovering.toIsQuotientMap.trivializationOfVAddDisjoint
    (@quotientMap_eq_iff_orbit) (sheetSet b) (isOpen_sheetSet b)
    (sheetSet_disjoint b)

theorem mem_coverTriv_baseSet (b : Base) : b ∈ (coverTriv b).baseSet := by
  change b ∈ quotientMap '' sheetSet b
  exact ⟨liftAt b, liftAt_mem_sheetSet b, quotientMap_liftAt b⟩

/-- The chosen atlas covers the literal Klein quotient pointwise. -/
theorem coverTriv_covers (x : Base) : ∃ b : Base, x ∈ (coverTriv b).baseSet :=
  ⟨x, mem_coverTriv_baseSet x⟩

end KleinGlideCoveringAtlas
end noncomputable section
