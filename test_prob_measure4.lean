import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef

open MeasureTheory

variable {α : Type*} [MeasurableSpace α] (P : ProbabilityMeasure α)

lemma test4 : IsFiniteMeasure P.val :=
  @IsProbabilityMeasure.toIsFiniteMeasure _ _ P.val P.prop

lemma test5 : (P.val : Measure α) Set.univ = 1 :=
  @measure_univ _ _ P.val P.prop

