import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

open MeasureTheory

variable {α : Type*} [MeasurableSpace α] (P : ProbabilityMeasure α)

noncomputable def probMeasureToUState (P : ProbabilityMeasure α) : FiniteMeasure α :=
  ⟨P.val, inferInstance⟩
