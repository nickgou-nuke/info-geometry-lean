namespace Omega.Discussion

/-- Exactness, cycle-pairing vanishing, and cohomology vanishing are equivalent under the
universal-coefficient/Ext-vanishing implication. -/
theorem paper_discussion_cubical_stokes_elimination_2cycle
    (exactnessCriterion pairingVanishesOnTwoCycles cohomologyClassVanishes
      universalCoefficientPackage : Prop)
    (universalCoefficientPackage_h : universalCoefficientPackage)
    (exactness_iff_cohomology : exactnessCriterion ↔ cohomologyClassVanishes)
    (cohomologyImpliesPairing :
      cohomologyClassVanishes → pairingVanishesOnTwoCycles)
    (pairingImpliesCohomology :
      pairingVanishesOnTwoCycles → universalCoefficientPackage →
        cohomologyClassVanishes) :
    (exactnessCriterion ↔ cohomologyClassVanishes) ∧
      (pairingVanishesOnTwoCycles ↔ cohomologyClassVanishes) ∧
      (exactnessCriterion ↔ pairingVanishesOnTwoCycles) := by
  have hPairingIffCohomology :
      pairingVanishesOnTwoCycles ↔ cohomologyClassVanishes := by
    constructor
    · intro hPairing
      exact pairingImpliesCohomology hPairing universalCoefficientPackage_h
    · intro hCohomology
      exact cohomologyImpliesPairing hCohomology
  have hExactnessIffPairing :
      exactnessCriterion ↔ pairingVanishesOnTwoCycles := by
    constructor
    · intro hExact
      exact hPairingIffCohomology.mpr (exactness_iff_cohomology.mp hExact)
    · intro hPairing
      exact exactness_iff_cohomology.mpr (hPairingIffCohomology.mp hPairing)
  exact ⟨exactness_iff_cohomology, hPairingIffCohomology, hExactnessIffPairing⟩

end Omega.Discussion
