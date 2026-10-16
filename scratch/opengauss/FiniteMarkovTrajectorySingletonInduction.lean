/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.QuantumContext.FiniteMarkovTransitionKernel
import Mathlib.Probability.Kernel.IonescuTulcea.PartialTraj

/-!
# Singleton masses for finite Markov trajectories

This scratch proposal starts the coordinate-product induction at horizon one,
using the final-coordinate extension in Mathlib's `partialTraj` recursion.
-/

noncomputable section

namespace InfoGeometry.QuantumContext.FiniteMarkovTrajectorySingletonInduction

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
open InfoGeometry.QuantumContext.FiniteMarkovTransitionKernel

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

local instance : MeasurableSpace ι := ⊤
local instance : MeasurableSingletonClass ι := inferInstance

/-- The state at time `k` in a trajectory indexed through time `n`. -/
def stateAt {n : ℕ} (x : Π _ : Finset.Iic n, ι) (k : Fin (n + 1)) : ι :=
  x ⟨k.val, Finset.mem_Iic.mpr (Nat.le_of_lt_succ k.isLt)⟩

/-- The horizon-one trajectory kernel gives the expected mass to a history
whose time-zero coordinate is the prescribed initial state. -/
theorem finiteTrajectoryKernel_one_singleton_mass
    (P : Matrix ι ι ℝ) (hP : P ∈ Matrix.rowStochastic ℝ ι) (i : ι)
    (x : Π _ : Finset.Iic 1, ι)
    (hx : stateAt x (0 : Fin (1 + 1)) = i) :
    finiteTrajectoryKernel P hP 0 1 (fun _ => i) {x} =
      ENNReal.ofReal (P i (stateAt x ⟨1, by omega⟩)) := by
  classical
  have hzero : (fun _ : Finset.Iic 0 => i) = fun _ => i := rfl
  change (Kernel.partialTraj (historyTransitionKernel P hP) 0 1) (fun _ => i) {x} = _
  rw [Kernel.partialTraj_succ_self]
  simp only [Kernel.map_apply' _ (by fun_prop) _ (by fun_prop)]
  simp [Kernel.id_prod_apply', historyTransitionKernel, Kernel.comp_apply,
    Kernel.deterministic_apply, transitionKernel_singleton, stateAt]

end InfoGeometry.QuantumContext.FiniteMarkovTrajectorySingletonInduction
