import Mathlib.Tactic

namespace Omega.POM

/-- Paper-facing wrapper for the uniform-lift KL isometry and its uniqueness characterization.
    thm:pom-uniform-lift-kl-isometry-uniqueness -/
theorem paper_pom_uniform_lift_kl_isometry_uniqueness
    (isometry uniqueness finiteSurjectionWitness fiberwiseUniformLiftExpansion
      innerFiberSumCollapse diracMassSectionTest pushforwardSupportSeparation
      twoPointMixtureKlPreservation : Prop)
    (finiteSurjectionWitness_h : finiteSurjectionWitness)
    (fiberwiseUniformLiftExpansion_h : fiberwiseUniformLiftExpansion)
    (innerFiberSumCollapse_h : innerFiberSumCollapse)
    (diracMassSectionTest_h : diracMassSectionTest)
    (pushforwardSupportSeparation_h : pushforwardSupportSeparation)
    (twoPointMixtureKlPreservation_h : twoPointMixtureKlPreservation)
    (deriveIsometry :
      finiteSurjectionWitness → fiberwiseUniformLiftExpansion → innerFiberSumCollapse → isometry)
    (deriveUniqueness :
      finiteSurjectionWitness → diracMassSectionTest →
        pushforwardSupportSeparation → twoPointMixtureKlPreservation → uniqueness) :
    isometry ∧ uniqueness := by
  have hIsometry : isometry :=
    deriveIsometry finiteSurjectionWitness_h fiberwiseUniformLiftExpansion_h
      innerFiberSumCollapse_h
  have hUniqueness : uniqueness :=
    deriveUniqueness finiteSurjectionWitness_h diracMassSectionTest_h
      pushforwardSupportSeparation_h twoPointMixtureKlPreservation_h
  exact ⟨hIsometry, hUniqueness⟩

end Omega.POM
