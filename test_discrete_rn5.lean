import Mathlib.MeasureTheory.Measure.MutuallySingular
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Average

open MeasureTheory
open scoped ENNReal

variable {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
variable (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
variable [HaveLebesgueDecomposition μ ν] (h : μ ≪ ν)

#check set_lintegral_singleton
#check setLIntegral_singleton
#check lintegral_indicator
