/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.QuantumContext.FiniteMarkovTransitionKernel
import InfoGeometry.QuantumContext.FiniteMarkovHittingPMFExpectation
import Mathlib.Probability.ProbabilityMassFunction.Basic

/-!
# Production trajectory law and recursively generated successor PMF

This scratch candidate compares the production `partialTraj` law pushed to
successor coordinates with the repository-owned finite successor-path PMF.
It proves the empty and one-step cases; the all-horizon bridge is a separate
induction target, not asserted here without its shift/composition step.
-/

noncomputable section

namespace InfoGeometry.QuantumContext.FiniteMarkovTrajectoryLawBridgeAttempt

open MeasureTheory ProbabilityTheory
open InfoGeometry.QuantumContext.FiniteMarkovTransitionKernel
open InfoGeometry.QuantumContext.FiniteMarkovHittingPMFExpectation

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

local instance : MeasurableSpace ι := ⊤
local instance : MeasurableSingletonClass ι := inferInstance

/-- Read a finite production history after time zero as successor states. -/
def trajectorySuccessors (n : ℕ) (x : Π _ : Finset.Iic n, ι) : Fin n → ι :=
  fun k => x ⟨k.val + 1, Finset.mem_Iic.mpr (Nat.succ_le_of_lt k.isLt)⟩

/-- Production trajectory measure on its successor-coordinate carrier. -/
def finiteTrajectorySuccessorLaw (P : Matrix ι ι ℝ)
    (hP : P ∈ Matrix.rowStochastic ℝ ι) (n : ℕ) (i : ι) : Measure (Fin n → ι) :=
  (finiteTrajectoryKernel P hP 0 n (fun _ => i)).map (trajectorySuccessors n)

/-- The empty production successor path agrees with the PMF owner. -/
theorem finiteTrajectorySuccessorLaw_zero (P : Matrix ι ι ℝ)
    (hP : P ∈ Matrix.rowStochastic ℝ ι) (i : ι) :
    finiteTrajectorySuccessorLaw P hP 0 i =
      (successorPathPMF P hP 0 i).toMeasure := by
  change Measure.map (trajectorySuccessors 0) (Kernel.id (fun _ => i)) =
    (PMF.pure Fin.elim0).toMeasure
  rw [Kernel.id_apply, Measure.map_dirac' (by fun_prop), PMF.toMeasure_pure]
  congr 1
  exact Subsingleton.elim _ _

/-- On one transition, the production successor-coordinate law is the
repository-owned recursively generated successor-path PMF. -/
theorem finiteTrajectorySuccessorLaw_one (P : Matrix ι ι ℝ)
    (hP : P ∈ Matrix.rowStochastic ℝ ι) (i : ι) :
    finiteTrajectorySuccessorLaw P hP 1 i =
      (successorPathPMF P hP 1 i).toMeasure := by
  change (finiteTrajectoryKernel P hP 0 1 (fun _ => i)).map
      (trajectorySuccessors 1) = (successorPathPMF P hP 1 i).toMeasure
  have hcoord : trajectorySuccessors 1 =
      (fun x : Π _ : Finset.Iic 1, ι => fun _ : Fin 1 =>
        x ⟨1, Finset.mem_Iic.mpr le_rfl⟩) := by
    funext x k
    simp [trajectorySuccessors]
  rw [hcoord]
  have hbase := finiteTrajectoryKernel_initial_oneStep_successor_law P hP i
  have hpmf : successorPathPMF P hP 1 i =
      (rowPMF P hP i).map (fun j => fun _ : Fin 1 => j) := by
    simp only [successorPathPMF, PMF.pure_map]
    change (rowPMF P hP i).bind
      (PMF.pure ∘ fun j => @Fin.cons 0 (fun _ => ι) j Fin.elim0) = _
    rw [PMF.bind_pure_comp]
    congr 1
    funext j
    funext k
    fin_cases k
    rfl
  rw [hpmf]
  exact hbase

end InfoGeometry.QuantumContext.FiniteMarkovTrajectoryLawBridgeAttempt
