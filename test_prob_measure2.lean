import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

open MeasureTheory

variable {α : Type*} [MeasurableSpace α] (P : ProbabilityMeasure α)

#check Measure.coe_zero
#check zero_ne_one
#check P.prop
#check P.prop.measure_univ
#check measure_univ (μ := P.val)
