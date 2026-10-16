/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.QuantumContext.FiniteMarkovTransitionKernel
import Mathlib.Probability.Kernel.IonescuTulcea.PartialTraj

/-!
# Singleton masses for finite Markov trajectory kernels

This scratch leaf develops an explicit coordinate product for the finite
trajectory kernel. It starts with the zero-horizon singleton calculation.
-/

noncomputable section

namespace InfoGeometry.QuantumContext.FiniteMarkovTrajectorySingletonMass

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
open InfoGeometry.QuantumContext.FiniteMarkovTransitionKernel

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

local instance : MeasurableSpace ι := ⊤
local instance : MeasurableSingletonClass ι := inferInstance

/-- Read the state at a finite time coordinate from a trajectory history. -/
def stateAt {n : ℕ} (x : Π _ : Finset.Iic n, ι) (k : Fin (n + 1)) : ι :=
  x ⟨k.val, Finset.mem_Iic.mpr (Nat.le_of_lt_succ k.isLt)⟩

/-- The product of the one-step transition masses along a history. -/
def trajectoryMassProduct (P : Matrix ι ι ℝ) (n : ℕ)
    (x : Π _ : Finset.Iic n, ι) : ℝ≥0∞ :=
  ∏ k : Fin n, ENNReal.ofReal
    (P (stateAt x k.castSucc) (stateAt x k.succ))

/-- At zero horizon the production trajectory is the unique extension of its
initial history, so its singleton mass is one. -/
theorem finiteTrajectoryKernel_zero_singleton_mass
    (P : Matrix ι ι ℝ) (hP : P ∈ Matrix.rowStochastic ℝ ι) (i : ι)
    (x : Π _ : Finset.Iic 0, ι)
    (hx : stateAt x (0 : Fin (0 + 1)) = i) :
    finiteTrajectoryKernel P hP 0 0 (fun _ => i) {x} =
      trajectoryMassProduct P 0 x := by
  have hxi : x = (fun _ => i) := by
    funext t
    have ht : t = ⟨0, Finset.mem_Iic.mpr (Nat.zero_le 0)⟩ :=
      Subsingleton.elim _ _
    rw [ht]
    simpa [stateAt] using hx
  subst x
  change Kernel.id (fun _ : Finset.Iic 0 => i) {fun _ : Finset.Iic 0 => i} = _
  rw [Kernel.id_apply]
  simp [trajectoryMassProduct]

end InfoGeometry.QuantumContext.FiniteMarkovTrajectorySingletonMass
