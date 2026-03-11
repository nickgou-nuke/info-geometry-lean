import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

open MeasureTheory

variable {α : Type*} [MeasurableSpace α] [Nonempty α] (P : PMF α)
variable (hz : FiniteMeasure.mass ⟨P.toMeasure, PMF.isFiniteMeasure P⟩ = 0)

example : False := by
  have h1 : P.toMeasure Set.univ = 0 := by
    exact hz
  have h2 : P.toMeasure Set.univ = 1 := PMF.toMeasure_apply_univ P
  rw [h2] at h1
  symm at h1
  exact ENNReal.zero_ne_one h1
