import InfoGeometry.Projective.Twistor.Basic.StatisticalFamily

open scoped ENNReal

namespace InfoGeometry.Information

open MeasureTheory

/--
Radon–Nikodym density of a model measure with respect to the dominating measure.
-/
noncomputable def rnDensity
    {α : Type*} [MeasurableSpace α] {Θ : Type*}
    (family : StatisticalFamily α Θ) (θ : Θ) : α → ℝ≥0∞ :=
  family.model θ |>.rnDeriv family.base

/-- Pointwise log-density (as a real-valued function) induced by RN density. -/
noncomputable def logDensity
    {α : Type*} [MeasurableSpace α] {Θ : Type*}
    (family : StatisticalFamily α Θ) (θ : Θ) : α → ℝ :=
  fun x => Real.log ((rnDensity family θ x).toReal)

/-- Log-likelihood as negative log-density.

This is the working `ℝ`-valued likelihood objective used in the rest of the project.
-/
noncomputable def logLikelihood
    {α : Type*} [MeasurableSpace α] {Θ : Type*}
    (family : StatisticalFamily α Θ) (θ : Θ) : α → ℝ :=
  fun x => -logDensity family θ x

lemma logLikelihood_eq_neg_logDensity
    {α : Type*} [MeasurableSpace α] {Θ : Type*}
    (family : StatisticalFamily α Θ) (θ : Θ) :
    logLikelihood family θ = fun x => -logDensity family θ x := by
  rfl

/-- RN recovery theorem from decomposition data: every model measure is `withDensity` its RN density. -/
lemma rnDensity_reconstruct
    {α : Type*} [MeasurableSpace α] {Θ : Type*}
    (family : StatisticalFamily α Θ) (θ : Θ) :
    family.base.withDensity (rnDensity family θ) = family.model θ := by
  letI : (family.model θ).HaveLebesgueDecomposition family.base := family.decomposition θ
  simpa [rnDensity] using
    (Measure.withDensity_rnDeriv_eq (μ := family.model θ) (ν := family.base) (family.dominated θ))

/-- The dominating measure is recovered from the base case of an open-domain family.
The construction below is useful to keep the open-parameter object readable at call sites.
-/
noncomputable def evalBaseLogLikelihood
    {α : Type*} [MeasurableSpace α]
    {n : ℕ} {U : OpenParameterDomain n}
    (family : EuclideanStatisticalFamily α n U)
    (θ : ParameterPoint n U) : α → ℝ :=
  logLikelihood family θ

end InfoGeometry.Information
