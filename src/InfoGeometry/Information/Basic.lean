import InfoGeometry.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.Topology.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2

open scoped ENNReal

namespace InfoGeometry.Information

open MeasureTheory

/--
An open parameter domain in `ℝ^n`, represented as a set with an explicit `IsOpen` proof.
-/
structure OpenParameterDomain (n : ℕ) where
  carrier : Set (EuclideanSpace ℝ (Fin n))
  isOpen : IsOpen carrier

/-- Parameter points are subtype points of the open chart. -/
abbrev ParameterPoint (n : ℕ) (U : OpenParameterDomain n) : Type _ :=
  {θ : EuclideanSpace ℝ (Fin n) // θ ∈ U.carrier}

/--
Parametric family of measures indexed by an arbitrary parameter space `Θ`, together with
an explicit dominating measure and decomposition certificates.
-/
structure StatisticalFamily (α : Type*) [MeasurableSpace α] (Θ : Type*) where
  base : Measure α
  model : Θ → Measure α
  dominated : ∀ θ, model θ ≪ base
  decomposition : ∀ θ, (model θ).HaveLebesgueDecomposition base

/-- Shorthand for Euclidean families on open charts in `ℝ^n`. -/
abbrev EuclideanStatisticalFamily
    (α : Type*) [MeasurableSpace α] (n : ℕ) (U : OpenParameterDomain n) :=
  StatisticalFamily α (ParameterPoint n U)

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

/-- Re-indexing a statistical family along a parameter map. -/
noncomputable def reparam
    {α : Type*} [MeasurableSpace α] {Θ Ξ : Type*}
    (family : StatisticalFamily α Θ) (f : Ξ → Θ) : StatisticalFamily α Ξ where
  base := family.base
  model := fun ξ => family.model (f ξ)
  dominated := fun ξ => family.dominated (f ξ)
  decomposition := fun ξ => family.decomposition (f ξ)

lemma dominated_reparam
    {α : Type*} [MeasurableSpace α] {Θ Ξ : Type*}
    (family : StatisticalFamily α Θ) (f : Ξ → Θ) (ξ : Ξ) :
    (reparam family f).model ξ ≪ (reparam family f).base := by
  dsimp [reparam]
  exact family.dominated (f ξ)

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
