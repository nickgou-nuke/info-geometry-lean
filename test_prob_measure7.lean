import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

open MeasureTheory

variable {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α] [Nonempty α]

abbrev UState (α : Type*) [MeasurableSpace α] := FiniteMeasure α

noncomputable def probMeasureToUState (P : ProbabilityMeasure α) : UState α :=
  letI : IsProbabilityMeasure P.val := P.prop
  ⟨P.val, inferInstance⟩

lemma probMeasureToUState_ne_zero (P : ProbabilityMeasure α) : probMeasureToUState P ≠ 0 := by
  intro h
  letI : IsProbabilityMeasure P.val := P.prop
  have h_mass : (probMeasureToUState P : Measure α) Set.univ = 1 := measure_univ
  have h_zero : (0 : Measure α) Set.univ = 0 := rfl
  have h_absurd : (probMeasureToUState P : Measure α) Set.univ = (0 : Measure α) Set.univ := by
    exact congrArg (fun m : FiniteMeasure α => (m : Measure α) Set.univ) h
  rw [h_mass, h_zero] at h_absurd
  exact zero_ne_one h_absurd.symm

