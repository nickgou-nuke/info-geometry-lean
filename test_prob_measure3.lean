import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

open MeasureTheory

variable {α : Type*} [MeasurableSpace α] (P : ProbabilityMeasure α)

lemma test1 : (P.val : Measure α) Set.univ = 1 := by
  have hP : IsProbabilityMeasure P.val := P.prop
  exact measure_univ

lemma test2 : (0 : Measure α) Set.univ = 0 := rfl

lemma test3 : (P.val : Measure α) Set.univ = 1 := P.prop.measure_univ
