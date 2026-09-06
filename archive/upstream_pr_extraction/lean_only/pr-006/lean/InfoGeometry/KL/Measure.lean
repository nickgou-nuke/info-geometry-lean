import Mathlib.InformationTheory.KullbackLeibler.Basic

/-!
# Measure KL Divergence

Measure-theoretic Kullback-Leibler divergence, re-exported from Mathlib's
`InformationTheory` namespace into the project namespace.
-/

open MeasureTheory
open scoped ENNReal

namespace InfoGeometry.KL

/-- Measure-theoretic KL divergence (`ℝ≥0∞`-valued). -/
noncomputable abbrev klDiv
    {α : Type _} [MeasurableSpace α]
    (μ ν : Measure α) : ℝ≥0∞ :=
  InformationTheory.klDiv μ ν

/- Explicit aliases to disambiguate from finite/discrete KL APIs. -/
noncomputable abbrev measureKlDiv
    {α : Type _} [MeasurableSpace α]
    (μ ν : Measure α) : ℝ≥0∞ :=
  klDiv μ ν

noncomputable abbrev klDivMeasure
    {α : Type _} [MeasurableSpace α]
    (μ ν : Measure α) : ℝ≥0∞ :=
  klDiv μ ν

lemma klDiv_of_not_ac
    {α : Type _} [MeasurableSpace α]
    {μ ν : Measure α}
    (h : ¬ μ ≪ ν) :
    klDiv μ ν = ∞ :=
  InformationTheory.klDiv_of_not_ac h

@[simp]
lemma klDiv_self
    {α : Type _} [MeasurableSpace α]
    (μ : Measure α) [SigmaFinite μ] :
    klDiv μ μ = 0 :=
  InformationTheory.klDiv_self μ

lemma klDiv_eq_zero_iff
    {α : Type _} [MeasurableSpace α]
    (μ ν : Measure α)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    klDiv μ ν = 0 ↔ μ = ν :=
  InformationTheory.klDiv_eq_zero_iff (μ := μ) (ν := ν)

end InfoGeometry.KL
