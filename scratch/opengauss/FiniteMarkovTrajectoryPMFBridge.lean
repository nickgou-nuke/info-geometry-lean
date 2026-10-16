/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.QuantumContext.FiniteMarkovTransitionKernel
import InfoGeometry.QuantumContext.FiniteMarkovHittingCost
import Mathlib.Probability.ProbabilityMassFunction.Basic

/-!
# Finite trajectory kernel and successor-state carrier bridge

This scratch candidate records the exact history-to-successor-coordinate
transport and the one-step endpoint marginal available from `partialTraj`.
It deliberately does not identify the full trajectory law with an independently
recursive PMF unless that measure equality is proved.
-/

noncomputable section

namespace InfoGeometry.QuantumContext.FiniteMarkovTrajectoryPMFBridge

open MeasureTheory ProbabilityTheory

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

local instance : MeasurableSpace ι := ⊤
local instance : MeasurableSingletonClass ι := inferInstance
local instance (n : ℕ) : MeasurableSpace (Fin n → ι) := ⊤
local instance (n : ℕ) : MeasurableSingletonClass (Fin n → ι) := inferInstance

private def rowPMF (P : Matrix ι ι ℝ)
    (hP : P ∈ Matrix.rowStochastic ℝ ι) (i : ι) : PMF ι :=
  PMF.ofFintype (fun j => ENNReal.ofReal (P i j)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg
      (fun j _ => Matrix.nonneg_of_mem_rowStochastic hP)]
    rw [Matrix.sum_row_of_mem_rowStochastic hP i]
    norm_num)

/-- Forget the initial state and read the later states of a history as a
`Fin n`-indexed successor path. -/
def trajectorySuccessors (n : ℕ) (x : Π _ : Finset.Iic n, ι) : Fin n → ι :=
  fun k => x ⟨k.val + 1, Finset.mem_Iic.mpr (Nat.succ_le_of_lt k.isLt)⟩

/-- Recursive candidate law on the `n` successor states, starting from `i`.
The carrier omits the fixed initial state, so `n` transitions correspond to
`n` successor coordinates and the production history has `n + 1` states. -/
def recursiveSuccessorPathPMF (P : Matrix ι ι ℝ)
    (hP : P ∈ Matrix.rowStochastic ℝ ι) :
    (n : ℕ) → ι → PMF (Fin n → ι)
  | 0, _ => PMF.pure Fin.elim0
  | n + 1, i => (rowPMF P hP i).bind fun j =>
      (recursiveSuccessorPathPMF P hP n j).map (Fin.cons j)

/-- Measure obtained from the production trajectory kernel, started at the
constant time-zero history and pushed to successor-state coordinates. -/
def finiteTrajectorySuccessorLaw (P : Matrix ι ι ℝ)
    (hP : P ∈ Matrix.rowStochastic ℝ ι) (n : ℕ) (i : ι) : Measure (Fin n → ι) :=
  (InfoGeometry.QuantumContext.FiniteMarkovTransitionKernel.finiteTrajectoryKernel
    P hP 0 n (fun _ => i)).map (trajectorySuccessors n)

/- The remaining full-law bridge is the equality
`finiteTrajectorySuccessorLaw P hP n i =
  (recursiveSuccessorPathPMF P hP n i).toMeasure`.
It is intentionally recorded as prose here, not as an unproved Lean
proposition. -/

/-- The final successor coordinate is the endpoint state of the history. -/
theorem trajectorySuccessors_last (n : ℕ) (x : Π _ : Finset.Iic (n + 1), ι) :
    trajectorySuccessors (n + 1) x ⟨n, Nat.lt_succ_self n⟩ =
      x ⟨n + 1, Finset.mem_Iic.mpr le_rfl⟩ := by
  simp [trajectorySuccessors]

/-- Existing `partialTraj` endpoint marginal, expressed at the Markov-kernel
owner boundary. This is a one-step conditional law, not yet the full path law. -/
theorem finiteTrajectory_succ_endpoint (P : Matrix ι ι ℝ)
    (hP : P ∈ Matrix.rowStochastic ℝ ι) (n : ℕ) :
    (InfoGeometry.QuantumContext.FiniteMarkovTransitionKernel.finiteTrajectoryKernel
      P hP n (n + 1)).map
      (fun x : Π _ : Finset.Iic (n + 1), ι =>
        x ⟨n + 1, Finset.mem_Iic.mpr le_rfl⟩) =
      InfoGeometry.QuantumContext.FiniteMarkovTransitionKernel.historyTransitionKernel
        P hP n :=
  InfoGeometry.QuantumContext.FiniteMarkovTransitionKernel.finiteTrajectoryKernel_succ_endpoint
    P hP n

end InfoGeometry.QuantumContext.FiniteMarkovTrajectoryPMFBridge
