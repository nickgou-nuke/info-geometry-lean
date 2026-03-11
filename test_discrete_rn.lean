import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Continuous

open MeasureTheory

variable {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
variable (μ ν : Measure α) [IsFiniteMeasure μ] [μ.HaveLebesgueDecomposition ν] (h : μ ≪ ν)

#check Measure.rnDeriv μ ν
