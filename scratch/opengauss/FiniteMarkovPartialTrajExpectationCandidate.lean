/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.QuantumContext.FiniteMarkovTransitionKernel
import InfoGeometry.QuantumContext.FiniteMarkovDirichletApproximation

/-!
# Finite trajectory endpoint marginal prototype

This scratch module proves the endpoint marginal of one finite `partialTraj`
extension. It is the kernel-level step needed to turn a path observable into
the existing one-step transition expectation. It makes no infinite-trajectory
or colimit expectation claim.
-/

namespace InfoGeometry.QuantumContext.FiniteMarkovPartialTrajExpectationCandidate

open ProbabilityTheory
open ProbabilityTheory.Kernel
open InfoGeometry.QuantumContext.FiniteMarkovTransitionKernel

local instance : MeasurableSpace ι := ⊤
local instance : MeasurableSingletonClass ι := inferInstance

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Extending a finite Markov history by one transition and observing its new
endpoint has exactly the row law selected by the previous endpoint. This is
the abstract `partialTraj` form underlying `finiteTrajectoryKernel`. -/
theorem partialTraj_succ_endpoint
    (P : Matrix ι ι ℝ) (hP : P ∈ Matrix.rowStochastic ℝ ι) (n : ℕ) :
    (partialTraj (X := fun _ => ι) (historyTransitionKernel P hP) n (n + 1)).map
      (fun x : Π _ : Finset.Iic (n + 1), ι =>
        x ⟨n + 1, Finset.mem_Iic.mpr le_rfl⟩) =
      historyTransitionKernel P hP n := by
  exact map_partialTraj_succ_self
    (X := fun _ => ι) (κ := historyTransitionKernel P hP) n

end InfoGeometry.QuantumContext.FiniteMarkovPartialTrajExpectationCandidate
