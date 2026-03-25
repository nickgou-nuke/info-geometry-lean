import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.LogLikelihoodRatio
import Mathlib.InformationTheory.KullbackLeibler.Basic

namespace Test

open scoped BigOperators ENNReal NNReal

structure EmpiricalCounts (α : Type*) where
  count : α → ℕ

instance {α : Type*} : CoeFun (EmpiricalCounts α) (fun _ => α → ℕ) where
  coe N := N.count

abbrev FinProb (α : Type*) := PMF α

/-- Convert nontrivial empirical counts into a canonical `FinProb`. -/
noncomputable def empiricalFinProb {α : Type*} [Fintype α] [Nonempty α]
    (N : EmpiricalCounts α) (h : 0 < ∑ x, N x) : FinProb α :=
  let total := ∑ x, (N x : ℝ)
  have hZ_pos : 0 < total := by
    have h' : (0 : ℝ) < ∑ x, (N x : ℝ) := by
      exact_mod_cast h
    simpa [total] using h'
  PMF.ofFintype (fun x => ENNReal.ofReal ((N x : ℝ) / total)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun x _ => div_nonneg (Nat.cast_nonneg _) hZ_pos.le)]
    rw [← Finset.sum_div, div_self hZ_pos.ne', ENNReal.ofReal_one])

end Test
