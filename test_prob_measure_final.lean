import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.MutuallySingular

open MeasureTheory

variable {α : Type*} [MeasurableSpace α] (P : ProbabilityMeasure α)

#check zero_ne_one
#check MeasureTheory.ProbabilityMeasure.toFiniteMeasure_normalize_eq_self
