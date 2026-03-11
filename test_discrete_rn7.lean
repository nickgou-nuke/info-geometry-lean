import InfoGeometry.Measure.Normalized
import Mathlib.MeasureTheory.Measure.MutuallySingular
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Decomposition.Lebesgue
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

set_option autoImplicit false

open MeasureTheory
open scoped ENNReal

variable {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]

theorem rnDeriv_pmf_eq_div
    (P Q : PMF α)
    [P.toMeasure.HaveLebesgueDecomposition Q.toMeasure]
    (hPQ : P.toMeasure.AbsolutelyContinuous Q.toMeasure) :
    P.toMeasure.rnDeriv Q.toMeasure =ᶠ[ae P.toMeasure] fun x => (P x : ℝ≥0∞) / (Q x : ℝ≥0∞) := by
  refine Filter.Eventually.of_forall ?_
  intro x
  by_cases hQ : Q x = 0
  · -- If Q x = 0, then by absolute continuity, P x = 0
    have hQ_meas : Q.toMeasure ({x} : Set α) = 0 := by
      rw [PMF.toMeasure_apply_singleton Q x (measurableSet_singleton x)]
      exact ENNReal.coe_eq_zero.mpr hQ
    have hP_meas : P.toMeasure ({x} : Set α) = 0 := hPQ hQ_meas
    have hP : P x = 0 := by
      have h_app := PMF.toMeasure_apply_singleton P x (measurableSet_singleton x)
      rw [hP_meas] at h_app
      exact ENNReal.coe_eq_zero.mp h_app.symm
    simp [hP, hQ]
  · -- If Q x ≠ 0, we can safely divide
    have hz : Q.toMeasure ({x} : Set α) ≠ 0 := by
      rw [PMF.toMeasure_apply_singleton Q x (measurableSet_singleton x)]
      exact ENNReal.coe_ne_zero.mpr hQ
    sorry
