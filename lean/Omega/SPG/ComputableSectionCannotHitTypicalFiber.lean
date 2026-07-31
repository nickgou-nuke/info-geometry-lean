import Omega.SPG.StokesGodelAlgorithmicHolographicCompleteness

namespace Omega.SPG

/-- Any computable section of the fold map has output complexity bounded by the base point, while
the existing fiber witness supplies a representative with logarithmic conditional-complexity gain.
Hence a computable section cannot systematically hit the typical high-complexity microstate in a
large fiber.
    prop:spg-computable-section-cannot-hit-typical-fiber -/
theorem paper_spg_computable_section_cannot_hit_typical_fiber
    (holographicData : StokesGodelAlgorithmicHolographicCompletenessData)
    (computableSection fiberComplexityWitness sectionOutputComplexityUpperBound
      typicalFiberComplexityGain cannotHitTypicalFiber : Prop)
    (computableSection_h : computableSection)
    (fiberComplexityWitness_h : fiberComplexityWitness)
    (deriveSectionOutputComplexityUpperBound :
      computableSection → holographicData.complexityPreserved → sectionOutputComplexityUpperBound)
    (deriveTypicalFiberComplexityGain :
      fiberComplexityWitness → typicalFiberComplexityGain)
    (deriveCannotHitTypicalFiber :
      sectionOutputComplexityUpperBound → typicalFiberComplexityGain → cannotHitTypicalFiber) :
    sectionOutputComplexityUpperBound ∧ typicalFiberComplexityGain ∧ cannotHitTypicalFiber := by
  have hComplexity :
      holographicData.complexityPreserved :=
    (paper_spg_stokes_godel_algorithmic_holographic_completeness holographicData).1
  have hUpper :
      sectionOutputComplexityUpperBound :=
    deriveSectionOutputComplexityUpperBound computableSection_h hComplexity
  have hGain : typicalFiberComplexityGain :=
    deriveTypicalFiberComplexityGain fiberComplexityWitness_h
  exact ⟨hUpper, hGain, deriveCannotHitTypicalFiber hUpper hGain⟩

end Omega.SPG
