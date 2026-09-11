import InfoGeometry.Measure.DiscreteRN
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.MeasureTheory.Measure.Decomposition.Lebesgue
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.Probability.ProbabilityMassFunction.Constructions

set_option autoImplicit false

open MeasureTheory
open scoped ENNReal

namespace InfoGeometry.Measure.RadonNikodymNormalForms

section Commutative

variable {α : Type*} [MeasurableSpace α]
variable {μ ν : Measure α}

/--
Canonical Radon-Nikodym normal form:
if `μ ≪ ν`, then `μ` is exactly `ν.withDensity (μ.rnDeriv ν)`.
-/
theorem normalForm_of_absolutelyContinuous
    [μ.HaveLebesgueDecomposition ν]
    (hμν : μ ≪ ν) :
    ν.withDensity (μ.rnDeriv ν) = μ :=
  Measure.withDensity_rnDeriv_eq μ ν hμν

/--
Absolute continuity is equivalent to admitting the RN normal form
`ν.withDensity (μ.rnDeriv ν) = μ`.
-/
theorem absolutelyContinuous_iff_normalForm
    [μ.HaveLebesgueDecomposition ν] :
    μ ≪ ν ↔ ν.withDensity (μ.rnDeriv ν) = μ :=
  Measure.absolutelyContinuous_iff_withDensity_rnDeriv_eq (μ := μ) (ν := ν)

/--
Lebesgue decomposition normal form:
every `μ` splits canonically into singular part plus RN-density part over `ν`.
-/
theorem lebesgueDecomposition_normalForm
    [μ.HaveLebesgueDecomposition ν] :
    μ = μ.singularPart ν + ν.withDensity (μ.rnDeriv ν) :=
  μ.haveLebesgueDecomposition_add ν

/--
Uniqueness of RN density in a pure-density representation:
if `μ = ν.withDensity f`, then `f = μ.rnDeriv ν` almost everywhere.
-/
theorem density_unique_ae
    [μ.HaveLebesgueDecomposition ν] [SigmaFinite ν]
    {f : α → ℝ≥0∞} (hf : Measurable f)
    (hrep : μ = ν.withDensity f) :
    f =ᵐ[ν] μ.rnDeriv ν := by
  have hrep' : μ = (0 : Measure α) + ν.withDensity f := by
    simp [hrep]
  simpa using
    (Measure.eq_rnDeriv (μ := μ) (ν := ν) (s := (0 : Measure α))
      hf Measure.MutuallySingular.zero_left hrep')

/--
Direct recovery theorem: if we build a measure via `withDensity`, its RN derivative
with respect to the base measure is the original density (a.e.).
-/
theorem rnDeriv_withDensity_eq_ae
    [SigmaFinite ν] {f : α → ℝ≥0∞} (hf : Measurable f) :
    (ν.withDensity f).rnDeriv ν =ᵐ[ν] f :=
  Measure.rnDeriv_withDensity ν hf

end Commutative

section Discrete

variable {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]

/--
Discrete normal form at a singleton:
the RN derivative equals the ratio of singleton masses.
-/
theorem rnDeriv_singleton_eq_mass_ratio
    (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    [μ.HaveLebesgueDecomposition ν]
    (x : α) (hμν : μ ≪ ν) (hνx : ν ({x} : Set α) ≠ 0) :
    μ.rnDeriv ν x = μ ({x} : Set α) / ν ({x} : Set α) :=
  InfoGeometry.Measure.DiscreteRN.rnDeriv_eq_div_of_singleton μ ν x hμν hνx

/--
For PMFs, the RN derivative is the pointwise ratio of masses almost everywhere.
-/
theorem rnDeriv_pmf_eq_pointwise_ratio
    (P Q : PMF α)
    [P.toMeasure.HaveLebesgueDecomposition Q.toMeasure]
    (hPQ : P.toMeasure.AbsolutelyContinuous Q.toMeasure) :
    P.toMeasure.rnDeriv Q.toMeasure =ᶠ[ae P.toMeasure]
      (fun x => (P x : ℝ≥0∞) / (Q x : ℝ≥0∞)) :=
  InfoGeometry.Measure.DiscreteRN.rnDeriv_pmf_eq_div P Q hPQ

end Discrete

end InfoGeometry.Measure.RadonNikodymNormalForms
