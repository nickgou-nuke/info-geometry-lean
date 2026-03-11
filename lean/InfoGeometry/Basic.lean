import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.LogLikelihoodRatio
import Mathlib.InformationTheory.KullbackLeibler.Basic

/-!
# Basic

Foundational types and definitions for InfoGeometry.
Consolidated canonical implementation using `PMF` as the foundation for finite laws,
enabling seamless integration with Mathlib's `Measure` and `ProbabilityMeasure` types.

## Main results
- `FinProb`: Alias for `PMF α`, the canonical discrete probability law.
- `potential`: Information-geometric potential defined as the negative log-likelihood ratio.
- `kl_div`: Kullback–Leibler divergence defined on general measures.
-/

namespace InfoGeometry

open scoped BigOperators ENNReal

/-- Empirical counts on a type. Consider replacing this by `α →₀ ℕ`
if finite support is intended. -/
structure EmpiricalCounts (α : Type*) where
  count : α → ℕ

instance {α : Type*} : CoeFun (EmpiricalCounts α) (fun _ => α → ℕ) where
  coe N := N.count

/--
Canonical finite probability distribution.
Defined as an alias to Mathlib's `PMF` to leverage existing discrete probability machinery.
-/
abbrev FinProb (α : Type*) := PMF α

namespace FinProb

variable {α : Type*}

/-- Construct a `FinProb` from a function on a finite type summing to `1`. -/
noncomputable def of_fintype [Fintype α]
    (f : α → ℝ≥0∞) (h : ∑ a, f a = 1) : FinProb α :=
  PMF.ofFintype f h

/-- Bridge to the probability-measure subtype. -/
noncomputable def to_probability_measure [MeasurableSpace α] (p : FinProb α) :
    MeasureTheory.ProbabilityMeasure α :=
  ⟨p.toMeasure, by infer_instance⟩

end FinProb

/-! ### Information-Theoretic Definitions -/

/-- Information-geometric potential: negative log-likelihood ratio. -/
noncomputable def potential
    {α : Type*} [MeasurableSpace α]
    (μ ν : MeasureTheory.Measure α) : α → ℝ :=
  -MeasureTheory.llr μ ν

/-- Measurability of the information-geometric potential. -/
theorem measurable_potential
    {α : Type*} [MeasurableSpace α]
    (μ ν : MeasureTheory.Measure α) :
    Measurable (potential μ ν) :=
  (MeasureTheory.measurable_llr μ ν).neg

/-- Same potential, restricted to probability measures. -/
noncomputable def potential_p
    {α : Type*} [MeasurableSpace α]
    (μ ν : MeasureTheory.ProbabilityMeasure α) : α → ℝ :=
  potential (μ : MeasureTheory.Measure α) (ν : MeasureTheory.Measure α)

/-- Measurability of the potential for probability measures. -/
theorem measurable_potential_p
    {α : Type*} [MeasurableSpace α]
    (μ ν : MeasureTheory.ProbabilityMeasure α) :
    Measurable (potential_p μ ν) :=
  measurable_potential (μ : MeasureTheory.Measure α) (ν : MeasureTheory.Measure α)

/-! ### Gauge-shift laws for the potential -/

theorem potential_smul_left_ae
    {α : Type*} [MeasurableSpace α]
    {μ ν : MeasureTheory.Measure α}
    [MeasureTheory.IsFiniteMeasure μ] [μ.HaveLebesgueDecomposition ν]
    (hμν : μ.AbsolutelyContinuous ν)
    (c : ℝ≥0∞) (hc : c ≠ 0) (hc_ne_top : c ≠ ⊤) :
    potential (c • μ) ν =ᵐ[μ] fun x => potential μ ν x - Real.log c.toReal := by
  filter_upwards [MeasureTheory.llr_smul_left hμν c hc hc_ne_top] with x hx
  simpa [potential, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
    congrArg (fun t : ℝ => -t) hx

theorem potential_smul_right_ae
    {α : Type*} [MeasurableSpace α]
    {μ ν : MeasureTheory.Measure α}
    [MeasureTheory.IsFiniteMeasure μ] [μ.HaveLebesgueDecomposition ν]
    (hμν : μ.AbsolutelyContinuous ν)
    (c : ℝ≥0∞) (hc : c ≠ 0) (hc_ne_top : c ≠ ⊤) :
    potential μ (c • ν) =ᵐ[μ] fun x => potential μ ν x + Real.log c.toReal := by
  filter_upwards [MeasureTheory.llr_smul_right hμν c hc hc_ne_top] with x hx
  simpa [potential, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
    congrArg (fun t : ℝ => -t) hx

/-- Canonical KL divergence on measures. -/
noncomputable def kl_div
    {α : Type*} [MeasurableSpace α]
    (μ ν : MeasureTheory.Measure α) : ℝ≥0∞ :=
  InformationTheory.klDiv μ ν

/-- Discrete convenience wrapper for KL divergence. -/
noncomputable def fin_kl_div
    {α : Type*} [MeasurableSpace α] (p q : FinProb α) : ℝ≥0∞ :=
  kl_div p.toMeasure q.toMeasure

/-- Discrete convenience wrapper for the potential. -/
noncomputable def fin_potential
    {α : Type*} [MeasurableSpace α] (p q : FinProb α) : α → ℝ :=
  potential p.toMeasure q.toMeasure

/-- Expectations under a discrete finite probability law. -/
noncomputable def expectation {α : Type*} [Fintype α]
    (p : FinProb α) (f : α → ℝ) : ℝ :=
  ∑ x, (p x).toReal * f x

/-- Pointwise log-density: `log p(x)`. -/
noncomputable def log_density {α : Type*} (p : FinProb α) (x : α) : ℝ :=
  Real.log (p x).toReal

/-- Pointwise surprisal: `-log p(x)`. -/
noncomputable def surprisal {α : Type*} (p : FinProb α) (x : α) : ℝ :=
  -log_density p x

/-- Discrete Shannon entropy. -/
noncomputable def entropy {α : Type*} [Fintype α] (p : FinProb α) : ℝ :=
  expectation p (surprisal p)

/-- Legacy aliases for backward compatibility. -/
abbrev ProbabilityDist (α : Type*) := FinProb α
abbrev StrictProbabilityDist (α : Type*) := FinProb α

noncomputable abbrev logDensity {α : Type*} (p : FinProb α) (x : α) : ℝ :=
  log_density p x

end InfoGeometry
