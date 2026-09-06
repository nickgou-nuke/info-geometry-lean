import InfoGeometry.Measure.Normalized
import Mathlib.MeasureTheory.Measure.MutuallySingular
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Decomposition.Lebesgue
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

set_option autoImplicit false

namespace InfoGeometry.Measure.DiscreteRN

open MeasureTheory
open scoped ENNReal

variable {α : Type*} [MeasurableSpace α] [Countable α] [MeasurableSingletonClass α]

omit [Countable α] in
lemma set_lintegral_singleton (ν : Measure α) (f : α → ℝ≥0∞) (x : α) :
    ∫⁻ y in ({x} : Set α), f y ∂ν = f x * ν ({x} : Set α) := by
  let s : Set α := {x}
  have hs : NullMeasurableSet s ν := (measurableSet_singleton x).nullMeasurableSet
  calc
    ∫⁻ y in s, f y ∂ν = ∫⁻ y, s.indicator f y ∂ν := by
      symm
      exact MeasureTheory.lintegral_indicator₀ hs f
    _ = ∫⁻ y, s.indicator (fun _ => f x) y ∂ν := by
      congr with y
      by_cases hy : y = x <;> simp [s, hy]
    _ = ∫⁻ y in s, (fun _ => f x) y ∂ν := by
      exact MeasureTheory.lintegral_indicator₀ hs (fun _ => f x)
    _ = f x * ν s := by
      rw [MeasureTheory.lintegral_const]
      simp [s]

omit [Countable α] in
/--
On a discrete space, the Radon–Nikodym derivative at a point of positive measure
is exactly the ratio of the singleton measures.
-/
theorem rnDeriv_eq_div_of_singleton
    (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    [μ.HaveLebesgueDecomposition ν] (x : α)
    (h_ac : μ ≪ ν) (hνx : ν ({x} : Set α) ≠ 0) :
    μ.rnDeriv ν x = μ ({x} : Set α) / ν ({x} : Set α) := by
  have hsingleton :
      μ ({x} : Set α) = μ.rnDeriv ν x * ν ({x} : Set α) := by
    calc
      μ ({x} : Set α) = ∫⁻ y in ({x} : Set α), μ.rnDeriv ν y ∂ν := by
        symm
        exact Measure.setLIntegral_rnDeriv' h_ac (measurableSet_singleton x)
      _ = μ.rnDeriv ν x * ν ({x} : Set α) := by
        exact set_lintegral_singleton ν (μ.rnDeriv ν) x
  have hνx_top : ν ({x} : Set α) ≠ ⊤ := by
    exact measure_ne_top ν ({x} : Set α)
  have hsingleton' :
      ν ({x} : Set α) * μ.rnDeriv ν x = μ ({x} : Set α) := by
    simpa [mul_comm] using hsingleton.symm
  exact (ENNReal.eq_div_iff hνx hνx_top).2 hsingleton'

omit [Countable α] in
/--
For probability mass functions, the abstract Radon–Nikodym derivative
coincides with the discrete coordinate ratio almost everywhere.
-/
theorem rnDeriv_pmf_eq_div
    (P Q : PMF α)
    [P.toMeasure.HaveLebesgueDecomposition Q.toMeasure]
    (hPQ : P.toMeasure.AbsolutelyContinuous Q.toMeasure) :
    P.toMeasure.rnDeriv Q.toMeasure =ᶠ[ae P.toMeasure]
      fun x => (P x : ℝ≥0∞) / (Q x : ℝ≥0∞) := by
  rw [Filter.EventuallyEq, MeasureTheory.ae_iff]
  rw [PMF.toMeasure_apply_eq_tsum, ENNReal.tsum_eq_zero]
  intro x
  by_cases hbad : P.toMeasure.rnDeriv Q.toMeasure x ≠ (P x : ℝ≥0∞) / (Q x : ℝ≥0∞)
  · have hPx : P x = 0 := by
      by_contra hPx
      have hQx : Q x ≠ 0 := by
        intro hQx
        have hQmeas : Q.toMeasure ({x} : Set α) = Q x := by
          simpa using Q.toMeasure_apply_singleton x (measurableSet_singleton x)
        have hQnull : Q.toMeasure ({x} : Set α) = 0 := by
          simpa [hQmeas] using hQx
        have hPnull : P.toMeasure ({x} : Set α) = 0 := hPQ hQnull
        have hPmeas : P.toMeasure ({x} : Set α) = P x := by
          simpa using P.toMeasure_apply_singleton x (measurableSet_singleton x)
        exact hPx <| by simpa [hPmeas] using hPnull
      have hPmeas : P.toMeasure ({x} : Set α) = P x := by
        simpa using P.toMeasure_apply_singleton x (measurableSet_singleton x)
      have hQmeas : Q.toMeasure ({x} : Set α) = Q x := by
        simpa using Q.toMeasure_apply_singleton x (measurableSet_singleton x)
      have hEq :
          P.toMeasure.rnDeriv Q.toMeasure x = (P x : ℝ≥0∞) / (Q x : ℝ≥0∞) := by
        simpa [hPmeas, hQmeas] using
          (rnDeriv_eq_div_of_singleton P.toMeasure Q.toMeasure x hPQ <| by
            simpa [hQmeas] using hQx)
      exact hbad hEq
    simp [hPx]
  · simp [hbad]

end InfoGeometry.Measure.DiscreteRN
