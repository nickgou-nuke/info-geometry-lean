import Mathlib.MeasureTheory.Measure.MutuallySingular
import Mathlib.MeasureTheory.Integral.Lebesgue
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

open MeasureTheory
open scoped ENNReal

variable {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
variable (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
variable [μ.HaveLebesgueDecomposition ν] (h : μ ≪ ν)

#check withDensity_apply
#check set_lintegral_singleton
#check Measure.rnDeriv
#check setLIntegral_singleton
#check lintegral_singleton
