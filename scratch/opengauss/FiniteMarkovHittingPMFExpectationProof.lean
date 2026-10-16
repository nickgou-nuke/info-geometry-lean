/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Probability.ProbabilityMassFunction.Integrals

/-!
# Finite PMF expectation proof for truncated Markov first-hit cost

This scratch proof attempts to identify the expectation on the finite
successor-path PMF with the existing Bellman approximant. It uses only finite
path carriers.
-/

noncomputable section

namespace InfoGeometry.QuantumContext.FiniteMarkovHittingPMFExpectationProof

open MeasureTheory ProbabilityTheory
open scoped ENNReal

variable {α β : Type*} [Fintype α] [Fintype β]
  [MeasurableSpace β] [MeasurableSingletonClass β]

/-- Finite expectation distributes over a PMF bind. -/
theorem integral_bind_fintype (p : PMF α) (q : α → PMF β) (f : β → ℝ) :
    ∫ b, f b ∂(p.bind q).toMeasure =
      ∑ a, (p a).toReal * ∫ b, f b ∂(q a).toMeasure := by
  simp_rw [PMF.integral_eq_sum]
  simp only [smul_eq_mul, PMF.bind_apply, tsum_fintype]
  calc
    (∑ b, (∑ a, p a * q a b).toReal * f b) =
        ∑ b, (∑ a, (p a).toReal * (q a b).toReal) * f b := by
      apply Finset.sum_congr rfl
      intro b hb
      rw [ENNReal.toReal_sum (fun a _ =>
        ne_of_lt (ENNReal.mul_lt_top (p.apply_lt_top a) ((q a).apply_lt_top b)))]
      simp_rw [ENNReal.toReal_mul]
    _ = ∑ b, ∑ a, ((p a).toReal * (q a b).toReal) * f b := by
      simp_rw [Finset.sum_mul]
    _ = ∑ a, ∑ b, ((p a).toReal * (q a b).toReal) * f b := by
      rw [Finset.sum_comm]
    _ = ∑ a, (p a).toReal * ∑ b, (q a b).toReal * f b := by
      apply Finset.sum_congr rfl
      intro a ha
      calc
        ∑ b, ((p a).toReal * (q a b).toReal) * f b =
            ∑ b, (p a).toReal * ((q a b).toReal * f b) := by
          apply Finset.sum_congr rfl
          intro b hb
          ring
        _ = (p a).toReal * ∑ b, (q a b).toReal * f b := by
          rw [← Finset.mul_sum]

end InfoGeometry.QuantumContext.FiniteMarkovHittingPMFExpectationProof
