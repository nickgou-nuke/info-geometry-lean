/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.QuantumContext.FiniteMarkovTransitionKernel
import InfoGeometry.QuantumContext.FiniteMarkovDirichletApproximation
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Probability.ProbabilityMassFunction.Integrals

/-!
# Finite PMF construction for truncated Markov first-hit cost

This prototype builds finite successor paths directly from the row PMFs of a
finite stochastic matrix. It is an alternate finite carrier to the kernel
trajectory API. No infinite path law or colimit/expectation identification is
asserted here.
-/

noncomputable section

namespace InfoGeometry.QuantumContext.FiniteMarkovHittingPMFCandidate

open MeasureTheory ProbabilityTheory
open scoped ENNReal

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

local instance : MeasurableSpace ι := ⊤
local instance : MeasurableSingletonClass ι := inferInstance

private def rowPMF (P : Matrix ι ι ℝ)
    (hP : P ∈ Matrix.rowStochastic ℝ ι) (i : ι) : PMF ι :=
  PMF.ofFintype (fun j => ENNReal.ofReal (P i j)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg
      (fun j _ => Matrix.nonneg_of_mem_rowStochastic hP)]
    rw [Matrix.sum_row_of_mem_rowStochastic hP i]
    norm_num)

/-- The law of `n` successive destination states, stored in time order. -/
def successorPathPMF (P : Matrix ι ι ℝ)
    (hP : P ∈ Matrix.rowStochastic ℝ ι) :
    (n : ℕ) → ι → PMF (Fin n → ι)
  | 0, _ => PMF.pure Fin.elim0
  | n + 1, i => (rowPMF P hP i).bind fun j =>
      (successorPathPMF P hP n j).map (Fin.cases j)

/-- Cost of the first hit, truncated to the number of successor states in
the finite path. The starting state is counted at time zero. -/
def pathFirstHitCost (target : ι) :
    (n : ℕ) → ι → (Fin n → ι) → ℝ
  | 0, _, _ => 0
  | n + 1, i, path =>
      if i = target then 0 else
        1 + pathFirstHitCost target n (path 0) (fun k => path k.succ)

/-- Expected truncated first-hit cost under the explicitly constructed
finite successor-path PMF. -/
def successorPathExpectedCost (P : Matrix ι ι ℝ)
    (hP : P ∈ Matrix.rowStochastic ℝ ι) (target : ι) (n : ℕ) (i : ι) : ℝ :=
  ∫ path, pathFirstHitCost target n i path ∂(successorPathPMF P hP n i).toMeasure

/-- The zero-step path law is concentrated on the unique empty path. -/
@[simp]
theorem successorPathPMF_zero (P : Matrix ι ι ℝ)
    (hP : P ∈ Matrix.rowStochastic ℝ ι) (i : ι) :
    successorPathPMF P hP 0 i = PMF.pure Fin.elim0 := rfl

/-- At zero horizon the pathwise cost vanishes. -/
@[simp]
theorem pathFirstHitCost_zero (target i : ι) (path : Fin 0 → ι) :
    pathFirstHitCost target 0 i path = 0 := rfl

end InfoGeometry.QuantumContext.FiniteMarkovHittingPMFCandidate
