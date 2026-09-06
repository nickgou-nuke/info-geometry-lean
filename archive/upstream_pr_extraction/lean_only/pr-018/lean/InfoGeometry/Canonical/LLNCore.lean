import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Probability.StrongLaw

/-!
# InfoGeometry.Canonical.LLNCore

Canonical core for SLLN/empirical convergence using mathlib probability results.
-/

namespace InfoGeometry.Canonical.LLN

open scoped BigOperators ProbabilityTheory
open Filter MeasureTheory ProbabilityTheory

/-- Empirical average of a real sequence over the first `n` samples. -/
noncomputable def empiricalAverage (X : Nat → Real) (n : Nat) : Real :=
  (n : Real)⁻¹ * Finset.sum (Finset.range n) X

/--
Strong-law convergence statement for a real-valued stochastic process on `(Ω, μ)`.
-/
def fixed_partition_slln {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (X : ℕ → Ω → ℝ) : Prop :=
  ∀ᵐ ω ∂μ, Tendsto (fun n : ℕ => (∑ i ∈ Finset.range n, X i ω) / n) atTop (nhds μ[X 0])

/--
`fixed_partition_slln` from pairwise-independence, identical distribution, and integrability.
This is exactly `ProbabilityTheory.strong_law_ae_real`.
-/
theorem fixed_partition_slln_holds
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (X : ℕ → Ω → ℝ) (hint : Integrable (X 0) μ)
    (hindep : Pairwise (fun i j => X i ⟂ᵢ[μ] X j))
    (hident : ∀ i, IdentDistrib (X i) (X 0) μ μ) :
    fixed_partition_slln μ X := by
  simpa [fixed_partition_slln] using
    (ProbabilityTheory.strong_law_ae_real (μ := μ) X hint hindep hident)

/-- Canonical alias used by downstream modules/docs. -/
def empirical_to_theoretical_slln {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (X : ℕ → Ω → ℝ) : Prop :=
  fixed_partition_slln μ X

/--
Almost-everywhere convergence of a ratio process to a Radon-Nikodym derivative target.
-/
def ae_tendsto_ratio_to_rnDeriv
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (ratio : ℕ → Ω → ℝ) (rnDeriv : Ω → ℝ) : Prop :=
  ∀ᵐ ω ∂μ, Tendsto (fun n : ℕ => ratio n ω) atTop (nhds (rnDeriv ω))

/-- Introduction rule for `ae_tendsto_ratio_to_rnDeriv`. -/
theorem ae_tendsto_ratio_to_rnDeriv_holds
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (ratio : ℕ → Ω → ℝ) (rnDeriv : Ω → ℝ)
    (h : ∀ᵐ ω ∂μ, Tendsto (fun n : ℕ => ratio n ω) atTop (nhds (rnDeriv ω))) :
    ae_tendsto_ratio_to_rnDeriv μ ratio rnDeriv :=
  h

end InfoGeometry.Canonical.LLN
