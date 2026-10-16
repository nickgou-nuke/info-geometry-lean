/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.QuantumContext.FiniteMarkovTransitionKernel

/-!
# One-step shift covariance for finite Markov histories

This scratch owner isolates the time-homogeneity fact needed to compare a
one-step extension after dropping its first coordinate with an extension of
the shifted initial history.  It proves equality of the corresponding
transition kernels from the endpoint law.  A full pushforward identity for
the trajectory measures is a separate result and is not asserted here.
-/

namespace InfoGeometry.QuantumContext.FiniteMarkovOneStepShiftCovariance

open ProbabilityTheory

/-- Reindex a history on times `0,...,n+1` by dropping time zero. -/
def shiftHistory {ι : Type*} (n : ℕ) (h : Π _ : Finset.Iic (n + 1), ι) :
    Π _ : Finset.Iic n, ι := fun k => h ⟨k.1 + 1, by
      have hk : k.1 ≤ n := Finset.mem_Iic.mp k.2
      exact Finset.mem_Iic.mpr (by omega)⟩

/-- The shifted history has the same endpoint as the original history. -/
theorem shiftHistory_endpoint {ι : Type*} (n : ℕ)
    (h : Π _ : Finset.Iic (n + 1), ι) :
    shiftHistory n h ⟨n, Finset.mem_Iic.mpr le_rfl⟩ =
      h ⟨n + 1, Finset.mem_Iic.mpr le_rfl⟩ := by
  rfl

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

local instance : MeasurableSpace ι := ⊤
local instance : MeasurableSingletonClass ι := inferInstance

/-- Time homogeneity: the one-step transition law after shifting a history
equals the transition law from the original history. -/
theorem shifted_historyTransitionKernel_apply_eq (P : Matrix ι ι ℝ)
    (hP : P ∈ Matrix.rowStochastic ℝ ι) (n : ℕ)
    (h : Π _ : Finset.Iic (n + 1), ι) :
    InfoGeometry.QuantumContext.FiniteMarkovTransitionKernel.historyTransitionKernel
        P hP n (shiftHistory n h) =
      InfoGeometry.QuantumContext.FiniteMarkovTransitionKernel.historyTransitionKernel
        P hP (n + 1) h := by
  simp only [InfoGeometry.QuantumContext.FiniteMarkovTransitionKernel.historyTransitionKernel,
    Kernel.comp_apply, Kernel.deterministic_apply]
  rw [shiftHistory_endpoint n h]

/-- The final-coordinate marginal of the shifted one-step trajectory agrees
with that of the fresh one-step trajectory from the shifted history. -/
theorem shifted_finiteTrajectoryKernel_endpoint_law (P : Matrix ι ι ℝ)
    (hP : P ∈ Matrix.rowStochastic ℝ ι) (n : ℕ)
    (h : Π _ : Finset.Iic (n + 1), ι) :
    (InfoGeometry.QuantumContext.FiniteMarkovTransitionKernel.finiteTrajectoryKernel
        P hP (n + 1) (n + 2) h).map
        (fun x : Π _ : Finset.Iic (n + 2), ι =>
          x ⟨n + 2, Finset.mem_Iic.mpr le_rfl⟩) =
      InfoGeometry.QuantumContext.FiniteMarkovTransitionKernel.historyTransitionKernel
        P hP n (shiftHistory n h) := by
  have he := congrArg (fun κ => κ h)
    (InfoGeometry.QuantumContext.FiniteMarkovTransitionKernel.finiteTrajectoryKernel_succ_endpoint
      P hP (n + 1))
  rw [Kernel.map_apply _ (by fun_prop) _] at he
  change _ = InfoGeometry.QuantumContext.FiniteMarkovTransitionKernel.historyTransitionKernel
    P hP (n + 1) h at he
  rw [shifted_historyTransitionKernel_apply_eq P hP n h]
  exact he

end InfoGeometry.QuantumContext.FiniteMarkovOneStepShiftCovariance
