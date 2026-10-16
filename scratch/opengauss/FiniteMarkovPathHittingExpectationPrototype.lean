/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.QuantumContext.FiniteMarkovTransitionKernel
import InfoGeometry.QuantumContext.FiniteMarkovDirichletApproximation

/-!
# Finite Markov first-hit path cost prototype

This scratch module isolates the finite pathwise cost and the one-step
expectation equation for the existing Bellman approximants. It deliberately
does not identify a categorical order-colimit with an infinite-path
expectation.
-/

namespace InfoGeometry.QuantumContext.FiniteMarkovPathHittingExpectationPrototype

open MeasureTheory ProbabilityTheory

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The first-hit time truncated by the length of a finite path. -/
def truncatedFirstHitCost (target : ι) : List ι → ℝ
  | [] => 0
  | state :: tail => if state = target then 0 else 1 + truncatedFirstHitCost target tail

theorem truncatedFirstHitCost_nonneg (target : ι) (path : List ι) :
    0 ≤ truncatedFirstHitCost target path := by
  induction path with
  | nil => simp [truncatedFirstHitCost]
  | cons state tail ih =>
      simp only [truncatedFirstHitCost]
      split
      · norm_num
      · linarith

theorem truncatedFirstHitCost_le_length (target : ι) (path : List ι) :
    truncatedFirstHitCost target path ≤ path.length := by
  induction path with
  | nil => simp [truncatedFirstHitCost]
  | cons state tail ih =>
      simp only [truncatedFirstHitCost, List.length_cons]
      split
      · norm_num
      · have hnonneg := truncatedFirstHitCost_nonneg target tail
        norm_num at *
        linarith

open InfoGeometry.QuantumContext.FiniteMarkovTransitionKernel
open InfoGeometry.QuantumContext.FiniteMarkovDirichletApproximation

/-- The Bellman successor is the one-step expected future truncated cost,
plus the current unit cost, away from the target. -/
theorem firstHitApproximation_succ_eq_transition_expectation
    (P : Matrix ι ι ℝ) (hP : P ∈ Matrix.rowStochastic ℝ ι)
    (target : ι) (n : ℕ) (i : ι) (hi : i ≠ target) :
    firstHitApproximation P target (n + 1) i =
      1 + ∫ j, firstHitApproximation P target n j ∂transitionKernel P hP i := by
  rw [firstHitApproximation_succ_of_ne P target n i hi,
    transitionKernel_integral_eq_mulVec P hP i
      (firstHitApproximation P target n)]

/-- At the target, the finite-horizon first-hit cost is zero, independently
of the next transition law. -/
theorem firstHitApproximation_succ_eq_target_expectation
    (P : Matrix ι ι ℝ) (target : ι) (n : ℕ) :
    firstHitApproximation P target (n + 1) target = 0 :=
  firstHitApproximation_target P target (n + 1)

end InfoGeometry.QuantumContext.FiniteMarkovPathHittingExpectationPrototype
