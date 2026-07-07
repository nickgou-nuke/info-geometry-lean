import InfoGeometry.Projective.Twistor.Basic.ParameterDomain
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym

open scoped ENNReal

namespace InfoGeometry.Information

open MeasureTheory

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

end InfoGeometry.Information
