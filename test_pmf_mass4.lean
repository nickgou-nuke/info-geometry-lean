import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

open MeasureTheory

variable {α : Type*} [MeasurableSpace α] [Nonempty α] (P : PMF α)

#check MeasureTheory.FiniteMeasure.mass_zero
#check MeasureTheory.FiniteMeasure.mass
#check PMF.toMeasure_apply_univ P
