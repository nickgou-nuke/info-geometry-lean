import proofs.KleinBottleOrbitQuotient
import Mathlib.Topology.Covering.Quotient

/-! # The torus glide quotient as a genuine two-sheeted covering -/

noncomputable section
namespace KleinGlideCovering

open KleinBrillouinBase KleinBottleOrbitQuotient

abbrev Deck2 := ZMod 2

def deckVAdd (g : Deck2) (k : BrillouinTorus) : BrillouinTorus :=
  if g.val = 0 then k else torusGlide k

lemma deck2_zero_or_one (g : Deck2) : g = 0 ∨ g = 1 := by
  fin_cases g
  · exact Or.inl rfl
  · exact Or.inr rfl

lemma deckVAdd_zero (k : BrillouinTorus) : deckVAdd 0 k = k := by
  simp [deckVAdd]

lemma deckVAdd_one (k : BrillouinTorus) : deckVAdd 1 k = torusGlide k := by
  simp [deckVAdd]

instance : VAdd Deck2 BrillouinTorus := ⟨deckVAdd⟩

instance : AddAction Deck2 BrillouinTorus where
  zero_vadd k := deckVAdd_zero k
  add_vadd g h k := by
    change deckVAdd (g + h) k = deckVAdd g (deckVAdd h k)
    rcases deck2_zero_or_one g with rfl | rfl <;>
      rcases deck2_zero_or_one h with rfl | rfl
    · rw [zero_add, deckVAdd_zero, deckVAdd_zero]
    · rw [zero_add, deckVAdd_one, deckVAdd_zero]
    · rw [add_zero, deckVAdd_zero, deckVAdd_one]
    · have h11 : (1 : Deck2) + 1 = 0 := by decide
      rw [h11]
      simpa [deckVAdd] using (torusGlide_involutive k).symm

instance : ContinuousConstVAdd Deck2 BrillouinTorus where
  continuous_const_vadd g := by
    rcases deck2_zero_or_one g with rfl | rfl
    · have hf : (fun x => deckVAdd 0 x) = id := by
        funext x
        exact deckVAdd_zero x
      change Continuous (fun x => deckVAdd 0 x)
      rw [hf]
      exact continuous_id
    · have hf : (fun x => deckVAdd 1 x) = torusGlide := by
        funext x
        exact deckVAdd_one x
      change Continuous (fun x => deckVAdd 1 x)
      rw [hf]
      exact torusGlide_continuous

theorem deck_orbit_relation (x y : BrillouinTorus) :
    x ∈ AddAction.orbit Deck2 y ↔ x = y ∨ x = torusGlide y := by
  constructor
  · rintro ⟨g, rfl⟩
    rcases deck2_zero_or_one g with rfl | rfl
    · exact Or.inl (by change deckVAdd 0 y = y; exact deckVAdd_zero y)
    · exact Or.inr (by change deckVAdd 1 y = torusGlide y; exact deckVAdd_one y)
  · rintro (hxy | hxy)
    · subst x
      exact ⟨0, by change deckVAdd 0 y = y; exact deckVAdd_zero y⟩
    · subst x
      exact ⟨1, by change deckVAdd 1 y = torusGlide y; exact deckVAdd_one y⟩

instance : IsCancelVAdd Deck2 BrillouinTorus where
  right_cancel' g h k eq := by
    rcases deck2_zero_or_one g with rfl | rfl <;>
      rcases deck2_zero_or_one h with rfl | rfl
    · rfl
    · exfalso
      change deckVAdd 0 k = deckVAdd 1 k at eq
      rw [deckVAdd_zero, deckVAdd_one] at eq
      exact torusGlide_ne_self k (by simpa using eq.symm)
    · exfalso
      change deckVAdd 1 k = deckVAdd 0 k at eq
      rw [deckVAdd_zero, deckVAdd_one] at eq
      exact torusGlide_ne_self k (by simpa using eq)
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
