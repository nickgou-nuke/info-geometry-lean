import Mathlib.MeasureTheory.Measure.MutuallySingular
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic

open MeasureTheory
open scoped ENNReal

variable {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
variable (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
variable [HaveLebesgueDecomposition μ ν] (h : μ ≪ ν)

lemma set_lintegral_singleton (f : α → ℝ≥0∞) (x : α) :
    ∫⁻ y in {x}, f y ∂ν = f x * ν {x} := by
  rw [← lintegral_indicator (measurableSet_singleton x) f]
  have h_eq : {x}.indicator f = fun y => f x * {x}.indicator 1 y := by
    ext y
    by_cases hy : y ∈ ({x} : Set α)
    · rw [Set.mem_singleton_iff] at hy
      subst hy
      simp
    · have hx : y ≠ x := by rintro rfl; exact hy rfl
      simp [hx]
  rw [h_eq]
  rw [lintegral_const_mul]
  · simp [lintegral_indicator]
  · apply Measurable.indicator measurable_const (measurableSet_singleton x)

lemma rnDeriv_singleton (x : α) :
    μ.rnDeriv ν x * ν {x} = (μ {x} : ℝ≥0∞) := by
  have h1 : ∫⁻ y in {x}, μ.rnDeriv ν y ∂ν = μ.rnDeriv ν x * ν {x} := by
    exact set_lintegral_singleton ν (μ.rnDeriv ν) x
  have h2 : ∫⁻ y in {x}, μ.rnDeriv ν y ∂ν = (ν.withDensity (μ.rnDeriv ν)) {x} := by
    symm
    exact withDensity_apply (μ.rnDeriv ν) (measurableSet_singleton x)
  have h3 : μ = ν.withDensity (μ.rnDeriv ν) := by
    have h_dec := μ.haveLebesgueDecomposition_add ν
    have h_sing : μ.singularPart ν = 0 := Measure.singularPart_eq_zero_of_ac h
    rw [h_sing, zero_add] at h_dec
    exact h_dec
  rw [h3]
  rw [← h2]
  exact h1.symm
