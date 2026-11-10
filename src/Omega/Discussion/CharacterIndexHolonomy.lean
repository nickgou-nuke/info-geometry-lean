import Mathlib.Tactic

namespace Omega.Discussion

section CharacterIndexHolonomy

variable {A : Type*} [AddGroup A]

/-- Holonomy readout of an additive character. -/
def characterHolonomy (ℓ : A →+ ℤ) (g : A) : ℤ := ℓ g

/-- Additive characters send sums in the source to sums of holonomies. -/
theorem characterHolonomy_add (ℓ : A →+ ℤ) (g h : A) :
    characterHolonomy ℓ (g + h) = characterHolonomy ℓ g + characterHolonomy ℓ h :=
  map_add ℓ g h

/-- Every homomorphism from an additive group to `ℤ` kills its additive commutators. -/
theorem characterHolonomy_additiveCommutator (ℓ : A →+ ℤ) (g h : A) :
    characterHolonomy ℓ (g + h - g - h) = 0 := by
  simp only [characterHolonomy, map_sub, map_add]
  abel

/-- Postcomposition preserves the additive law of the holonomy readout. -/
theorem characterHolonomy_postcompose_add (χ : ℤ →+ ℤ) (ℓ : A →+ ℤ) (g h : A) :
    characterHolonomy (χ.comp ℓ) (g + h) =
      χ (characterHolonomy ℓ g) + χ (characterHolonomy ℓ h) := by
  change χ (ℓ (g + h)) = χ (ℓ g) + χ (ℓ h)
  rw [map_add, map_add]

/-- Postcomposition also annihilates source commutators in the holonomy readout. -/
theorem characterHolonomy_postcompose_additiveCommutator
    (χ : ℤ →+ ℤ) (ℓ : A →+ ℤ) (g h : A) :
    characterHolonomy (χ.comp ℓ) (g + h - g - h) = 0 := by
  exact characterHolonomy_additiveCommutator (χ.comp ℓ) g h

/-- A character-valued additive holonomy factors through the abelianization
at the level of its readout: it is additive and vanishes on additive
commutators, and both properties persist under postcomposition. -/
theorem paper_discussion_character_index_holonomy
    (χ : ℤ →+ ℤ) (ℓ : A →+ ℤ) (g h : A) :
    characterHolonomy ℓ (g + h) = characterHolonomy ℓ g + characterHolonomy ℓ h ∧
      characterHolonomy ℓ (g + h - g - h) = 0 ∧
      characterHolonomy (χ.comp ℓ) (g + h) =
        χ (characterHolonomy ℓ g) + χ (characterHolonomy ℓ h) ∧
      characterHolonomy (χ.comp ℓ) (g + h - g - h) = 0 := by
  exact ⟨characterHolonomy_add ℓ g h,
    characterHolonomy_additiveCommutator ℓ g h,
    characterHolonomy_postcompose_add χ ℓ g h,
    characterHolonomy_postcompose_additiveCommutator χ ℓ g h⟩

end CharacterIndexHolonomy

end Omega.Discussion
