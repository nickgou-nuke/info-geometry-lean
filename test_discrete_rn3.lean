import Mathlib.MeasureTheory.Measure.MutuallySingular
import Mathlib.MeasureTheory.Integral.Lebesgue
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

open MeasureTheory
open scoped ENNReal

variable {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
variable (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
variable [HaveLebesgueDecomposition μ ν] (h : μ ≪ ν)

lemma rnDeriv_singleton (x : α) :
    μ.rnDeriv ν x * ν {x} = (μ {x} : ℝ≥0∞) := by
  have h1 : ∫⁻ y in {x}, μ.rnDeriv ν y ∂ν = μ.rnDeriv ν x * ν {x} := by
    exact setLIntegral_singleton (μ.rnDeriv ν) x
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

