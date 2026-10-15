import InfoGeometry.Topology.KleinBottleOrbitQuotient
import Mathlib.Topology.Covering.Quotient

/-! # The torus glide quotient as a genuine two-sheeted covering -/

noncomputable section
namespace KleinGlideCovering

open KleinBrillouinBase KleinBottleOrbitQuotient

abbrev Deck2 := ZMod 2

def deckVAdd (g : Deck2) (k : BrillouinTorus) : BrillouinTorus :=
  if g.val = 0 then k else torusGlide k

instance : VAdd Deck2 BrillouinTorus := ⟨deckVAdd⟩

instance : AddAction Deck2 BrillouinTorus where
  zero_vadd k := by
    change deckVAdd 0 k = k
    simp [deckVAdd]
  add_vadd g h k := by
    change (if (g + h).val = 0 then k else torusGlide k) =
      if g.val = 0 then (if h.val = 0 then k else torusGlide k)
      else torusGlide (if h.val = 0 then k else torusGlide k)
    rw [ZMod.val_add]
    have hg : g.val = 0 ∨ g.val = 1 := by have := ZMod.val_lt g; omega
    have hh : h.val = 0 ∨ h.val = 1 := by have := ZMod.val_lt h; omega
    rcases hg with hg | hg <;> rcases hh with hh | hh <;>
      simp [hg, hh]
    all_goals exact (torusGlide_involutive k).symm

instance : ContinuousConstVAdd Deck2 BrillouinTorus where
  continuous_const_vadd g := by
    change Continuous (fun k => if g.val = 0 then k else torusGlide k)
    by_cases hg : g.val = 0
    · exact continuous_id.congr (fun k => by simp [hg])
    · exact torusGlide_continuous.congr (fun k => by simp [hg])

theorem deck_orbit_relation (x y : BrillouinTorus) :
    x ∈ AddAction.orbit Deck2 y ↔ x = y ∨ x = torusGlide y := by
  constructor
  · rintro ⟨g, rfl⟩
    change deckVAdd g y = y ∨ deckVAdd g y = torusGlide y
    by_cases hg : g.val = 0
    · exact Or.inl (by simp [deckVAdd, hg])
    · exact Or.inr (by simp [deckVAdd, hg])
  · rintro (hxy | hxy)
    · subst x
      refine ⟨0, ?_⟩
      change deckVAdd 0 y = y
      simp [deckVAdd]
    · subst x
      refine ⟨1, ?_⟩
      have hv : (1 : Deck2).val = 1 := by norm_num [ZMod.val_one_eq_one_mod]
      change deckVAdd 1 y = torusGlide y
      simp [deckVAdd, hv]

instance : IsCancelVAdd Deck2 BrillouinTorus where
  right_cancel' g h k eq := by
    change deckVAdd g k = deckVAdd h k at eq
    by_cases hg : g.val = 0 <;> by_cases hh : h.val = 0
    · apply ZMod.val_injective 2
      exact hg.trans hh.symm
    · have hh1 : h.val = 1 := by have := ZMod.val_lt h; omega
      have heq : k = torusGlide k := by simpa [deckVAdd, hg, hh] using eq
      exfalso
      exact (torusGlide_ne_self k) heq.symm
    · have hg1 : g.val = 1 := by have := ZMod.val_lt g; omega
      have heq : torusGlide k = k := by simpa [deckVAdd, hg, hh] using eq
      exfalso
      exact (torusGlide_ne_self k) heq
    · apply ZMod.val_injective 2
      have hg1 : g.val = 1 := by have := ZMod.val_lt g; omega
      have hh1 : h.val = 1 := by have := ZMod.val_lt h; omega
      exact hg1.trans hh1.symm

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
