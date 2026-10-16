/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.QuantumContext.FiniteMarkovTransitionKernel
import Mathlib.Probability.Kernel.IonescuTulcea.PartialTraj

/-!
# Horizon-one singleton evaluation for the finite Markov trajectory kernel

The statement is restricted to one transition. The proof follows the
final-coordinate extension used by Mathlib's `partialTraj` construction.
-/

noncomputable section

namespace InfoGeometry.QuantumContext.FiniteMarkovPartialTrajSingletonEval

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open InfoGeometry.QuantumContext.FiniteMarkovTransitionKernel

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

local instance : MeasurableSpace ι := ⊤
local instance : MeasurableSingletonClass ι := inferInstance

/-- Read a natural-time coordinate of a finite trajectory. -/
def trajectoryState {n : ℕ} (x : Π _ : Finset.Iic n, ι) (k : Fin (n + 1)) : ι :=
  x ⟨k.val, Finset.mem_Iic.mpr (Nat.le_of_lt_succ k.isLt)⟩

/-- At horizon one, a trajectory from state `i` assigns the matrix transition
mass from `i` to the time-one coordinate of the requested history. -/
theorem finiteTrajectoryKernel_one_singleton
    (P : Matrix ι ι ℝ) (hP : P ∈ Matrix.rowStochastic ℝ ι) (i : ι)
    (x : Π _ : Finset.Iic 1, ι)
    (hstart : x ⟨0, Finset.mem_Iic.mpr (by omega)⟩ = i) :
    finiteTrajectoryKernel P hP 0 1 (fun _ => i) {x} =
      ENNReal.ofReal
        (P i (x ⟨1, Finset.mem_Iic.mpr (by omega)⟩)) := by
  classical
  change (Kernel.partialTraj (historyTransitionKernel P hP) 0 1)
    (fun _ => i) {x} = _
  rw [Kernel.partialTraj_succ_self]
  simp [Kernel.map_apply', Kernel.id_prod_apply', historyTransitionKernel,
    Kernel.comp_apply, Kernel.deterministic_apply, transitionKernel_singleton,
    trajectoryState, hstart]

end InfoGeometry.QuantumContext.FiniteMarkovPartialTrajSingletonEval
