import proofs.KleinGlideCoveringAtlas

/-!
# Multiplicative presentation of the two-sheeted deck covering

This is the multiplicative wrapper requested by the generic Mathlib
`IsQuotientCoveringMap` API.  It is proved equivalent to the already certified
additive `ZMod 2` covering, not introduced as a second orbit geometry.
-/

noncomputable section
namespace KleinGlideMultiplicativeCovering

open Topology
open KleinBrillouinBase KleinBottleOrbitQuotient KleinGlideCovering

abbrev DeckMul := Multiplicative Deck2

instance : SMul DeckMul BrillouinTorus where
  smul g k := g.toAdd +ᵥ k

instance : MulAction DeckMul BrillouinTorus where
  one_smul k := by change (0 : Deck2) +ᵥ k = k; exact zero_vadd _ _
  mul_smul g h k := by
    change (g.toAdd + h.toAdd) +ᵥ k = g.toAdd +ᵥ (h.toAdd +ᵥ k)
    exact add_vadd _ _ _

instance : ContinuousConstSMul DeckMul BrillouinTorus where
  continuous_const_smul g := continuous_const_vadd g.toAdd

theorem mul_orbit_relation (x y : BrillouinTorus) :
    x ∈ MulAction.orbit DeckMul y ↔ x = y ∨ x = torusGlide y := by
  constructor
  · rintro ⟨g, rfl⟩
    obtain ⟨a, rfl⟩ : ∃ a : Deck2, Multiplicative.ofAdd a = g :=
      ⟨g.toAdd, rfl⟩
    fin_cases a
    · left
      change deckVAdd 0 y = y
      simp [deckVAdd]
    · right
      change deckVAdd 1 y = torusGlide y
      simp [deckVAdd]
  · rintro (rfl | rfl)
    · exact ⟨1, one_smul _ _⟩
    · refine ⟨Multiplicative.ofAdd (1 : Deck2), ?_⟩
      change deckVAdd 1 y = torusGlide y
      simp [deckVAdd]

theorem quotientMap_eq_iff_mulOrbit (x y : BrillouinTorus) :
    quotientMap x = quotientMap y ↔ x ∈ MulAction.orbit DeckMul y := by
  rw [quotientMap_eq_iff, mul_orbit_relation]
  constructor
  · rintro (rfl | h)
    · exact Or.inl rfl
    · right
      rw [h, torusGlide_involutive]
  · rintro (rfl | h)
    · exact Or.inl rfl
    · right
      rw [h, torusGlide_involutive]

/-- The literal quotient map as a native multiplicative quotient covering. -/
theorem quotientMap_isQuotientCovering :
    IsQuotientCoveringMap quotientMap DeckMul := by
  refine
    { toIsQuotientMap := quotientMap_isQuotient
      continuous_const_smul := fun g ↦ continuous_const_vadd g.toAdd
      apply_eq_iff_mem_orbit := fun {e₁ e₂} ↦ quotientMap_eq_iff_mulOrbit e₁ e₂
      disjoint := ?_ }
  intro k
  obtain ⟨U, hkU, hU⟩ := quotientMap_isAddQuotientCovering.disjoint k
  refine ⟨U, hkU, ?_⟩
  intro g hg
  have hzero : g.toAdd = 0 := hU g.toAdd (by simpa using hg)
  simpa using congrArg Multiplicative.ofAdd hzero

theorem quotientMap_isCovering_mul : IsCoveringMap quotientMap :=
  quotientMap_isQuotientCovering.isCoveringMap

/-- Multiplicative local trivialization extracted by Mathlib's generic
`trivializationOfSMulDisjoint` constructor. -/
noncomputable def multiplicativeCoverTriv (b : KleinBrillouinQuotient) :
    Trivialization DeckMul quotientMap := by
  exact quotientMap_isQuotient.trivializationOfSMulDisjoint
    (fun {e₁ e₂} ↦ quotientMap_eq_iff_mulOrbit e₁ e₂)
    (KleinGlideCoveringAtlas.sheetSet b)
    (KleinGlideCoveringAtlas.isOpen_sheetSet b)
    (by
      intro g hg
      have hz : g.toAdd = 0 :=
        KleinGlideCoveringAtlas.sheetSet_disjoint b g.toAdd (by simpa using hg)
      simpa using congrArg Multiplicative.ofAdd hz)

theorem multiplicativeCoverTriv_baseSet (b : KleinBrillouinQuotient) :
    (multiplicativeCoverTriv b).baseSet =
      (KleinGlideCoveringAtlas.coverTriv b).baseSet := rfl

/-- The multiplicative and additive chart changes are literally the same
two-sheet permutation after applying `toAdd`. -/
theorem multiplicativeCoverTriv_coordChange_toAdd
    (i j x : KleinBrillouinQuotient) (g : Deck2) :
    ((multiplicativeCoverTriv i).coordChange (multiplicativeCoverTriv j) x
      (Multiplicative.ofAdd g)).toAdd =
      (KleinGlideCoveringAtlas.coverTriv i).coordChange
        (KleinGlideCoveringAtlas.coverTriv j) x g := rfl

end KleinGlideMultiplicativeCovering
end noncomputable section
