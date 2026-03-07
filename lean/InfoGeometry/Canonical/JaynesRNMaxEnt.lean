import InfoGeometry.MaxEnt.JaynesRNMaxEnt

/-!
# InfoGeometry.Canonical.JaynesRNMaxEnt

Canonical facade for Radon-Nikodym/Jaynes maximum-entropy constructions.
-/

namespace InfoGeometry.Canonical.JaynesRNMaxEnt

export InfoGeometry.MaxEnt.JaynesRNMaxEnt (
  MomentFamily
  Satisfies
  SatisfiesIntegrable
  FeasibleSet
  FeasibleSetIntegrable
  FeasibleSetIntegrable_subset_FeasibleSet
  objectiveKL
  potential
  partitionFunction
  PartitionIntegrable
  gibbsMeasure
  gibbsMeasure_ac
  aemeasurable_potential
  rnDeriv_gibbsMeasure_eq
  partitionFunction_nonneg
  rnDeriv_gibbsMeasure_toReal_eq
  gibbs
  gibbs_minimizes_kl
  GibbsMinimizesKL
)

variable {Ω : Type*} [MeasurableSpace Ω]

@[simp] theorem objectiveKL_def
    (μ₀ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ₀]
    (P : MeasureTheory.ProbabilityMeasure Ω) :
    objectiveKL (μ₀ := μ₀) P
      = InformationTheory.klDiv (P : MeasureTheory.Measure Ω) μ₀ := rfl

end InfoGeometry.Canonical.JaynesRNMaxEnt
