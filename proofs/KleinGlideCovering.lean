import proofs.KleinBottleOrbitQuotient
import Mathlib.Topology.Covering.Quotient

/-! # The torus glide quotient as a genuine two-sheeted covering -/

noncomputable section
namespace KleinGlideCovering

open KleinBrillouinBase KleinBottleOrbitQuotient

abbrev Deck2 := ZMod 2

def deckVAdd (g : Deck2) (k : BrillouinTorus) : BrillouinTorus :=
  if g = 0 then k else torusGlide k

instance : VAdd Deck2 BrillouinTorus := ⟨deckVAdd⟩

instance : AddAction Deck2 BrillouinTorus where
  zero_vadd k := by change deckVAdd 0 k = k; simp [deckVAdd]
  add_vadd g h k := by
    change deckVAdd (g + h) k = deckVAdd g (deckVAdd h k)
    have h11 : (1 + 1 : Deck2) = 0 := by native_decide
    fin_cases g <;> fin_cases h <;>
      simp [deckVAdd, h11, torusGlide_involutive]
    exact (torusGlide_involutive k).symm

instance : ContinuousConstVAdd Deck2 BrillouinTorus where
  continuous_const_vadd g := by
    change Continuous (deckVAdd g)
    fin_cases g
    · simpa [deckVAdd] using
        (continuous_id : Continuous (id : BrillouinTorus → BrillouinTorus))
    · simpa [deckVAdd] using torusGlide_continuous

theorem deck_orbit_relation (x y : BrillouinTorus) :
    x ∈ AddAction.orbit Deck2 y ↔ x = y ∨ x = torusGlide y := by
  constructor
  · rintro ⟨g, rfl⟩
    fin_cases g
    · exact Or.inl (by simp [deckVAdd])
    · right; change deckVAdd 1 y = torusGlide y; simp [deckVAdd]
  · rintro (rfl | rfl)
    · exact ⟨0, by simp [deckVAdd]⟩
    · refine ⟨1, ?_⟩
      change deckVAdd 1 y = torusGlide y
      simp [deckVAdd]

instance : IsCancelVAdd Deck2 BrillouinTorus where
  right_cancel' g h k eq := by
    fin_cases g <;> fin_cases h
    · rfl
    · exfalso
      exact torusGlide_ne_self k (by simpa [deckVAdd] using eq.symm)
    · exfalso
      exact torusGlide_ne_self k (by simpa [deckVAdd] using eq)
    · rfl

/-- The existing orbit quotient agrees exactly with the group orbit relation. -/
theorem quotientMap_eq_iff_orbit (x y : BrillouinTorus) :
    quotientMap x = quotientMap y ↔ x ∈ AddAction.orbit Deck2 y := by
  rw [quotientMap_eq_iff, deck_orbit_relation]
  constructor
  · rintro (rfl | h)
    · exact Or.inl rfl
    · right
      rw [h, torusGlide_involutive]
  · rintro (rfl | h)
    · exact Or.inl rfl
    · right
      rw [h, torusGlide_involutive]

/-- The torus projection is a quotient covering map with deck group `ZMod 2`. -/
theorem quotientMap_isAddQuotientCovering :
    IsAddQuotientCoveringMap quotientMap Deck2 :=
  quotientMap_isQuotient.isAddQuotientCoveringMap_of_properlyDiscontinuousVAdd
    (@quotientMap_eq_iff_orbit)

theorem quotientMap_isCovering : IsCoveringMap quotientMap :=
  quotientMap_isAddQuotientCovering.isCoveringMap

theorem quotientMap_isOpen : IsOpenMap quotientMap :=
  quotientMap_isAddQuotientCovering.isOpenQuotientMap.isOpenMap

end KleinGlideCovering
end noncomputable section
