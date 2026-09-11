import Mathlib.InformationTheory.KullbackLeibler.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra

open MeasureTheory
open scoped ENNReal

namespace InfoGeometry.Information.NativeRelativeEntropy

theorem klDiv_pos_iff
    {α : Type*} [MeasurableSpace α]
    (μ ν : Measure α)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    0 < InformationTheory.klDiv μ ν ↔ μ ≠ ν := by
  rw [pos_iff_ne_zero, ne_eq, InformationTheory.klDiv_eq_zero_iff]

theorem klDiv_toReal_pos
    {α : Type*} [MeasurableSpace α]
    (μ ν : Measure α)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hne : μ ≠ ν)
    (hac : μ ≪ ν)
    (hint : Integrable (llr μ ν) μ) :
    0 < (InformationTheory.klDiv μ ν).toReal := by
  apply ENNReal.toReal_pos
  · exact (InformationTheory.klDiv_eq_zero_iff.not.mpr hne)
  · exact InformationTheory.klDiv_ne_top_iff.mpr ⟨hac, hint⟩

theorem symmetric_klDiv_eq_zero_iff
    {α : Type*} [MeasurableSpace α]
    (μ ν : Measure α)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    InformationTheory.klDiv μ ν + InformationTheory.klDiv ν μ = 0 ↔
      μ = ν := by
  simp only [add_eq_zero, InformationTheory.klDiv_eq_zero_iff]
  exact ⟨fun h => h.1, fun h => ⟨h, h.symm⟩⟩

theorem symmetric_klDiv_pos_iff
    {α : Type*} [MeasurableSpace α]
    (μ ν : Measure α)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    0 < InformationTheory.klDiv μ ν + InformationTheory.klDiv ν μ ↔
      μ ≠ ν := by
  rw [pos_iff_ne_zero, ne_eq, symmetric_klDiv_eq_zero_iff]

end InfoGeometry.Information.NativeRelativeEntropy
