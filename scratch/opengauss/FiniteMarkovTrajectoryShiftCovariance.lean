/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.QuantumContext.FiniteMarkovTransitionKernel

/-!
# Time-shift covariance candidate for finite Markov trajectory kernels

The source history begins at time `1`; the target history begins at time `0`.
The map below drops the source time-zero coordinate and renumbers all later
coordinates. The all-horizon covariance is the intended induction target; this
file currently proves its zero-horizon base case only.
-/

noncomputable section

namespace InfoGeometry.QuantumContext.FiniteMarkovTrajectoryShiftCovariance

open MeasureTheory ProbabilityTheory
open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

local instance : MeasurableSpace ι := ⊤
local instance : MeasurableSingletonClass ι := inferInstance

/-- Drop time zero and renumber the remaining coordinates of a history. -/
def shiftHistory (n : ℕ) (x : Π _ : Iic (n + 1), ι) : Π _ : Iic n, ι :=
  fun k => x ⟨k.val + 1, mem_Iic.mpr (Nat.succ_le_succ (mem_Iic.mp k.2))⟩

/-- The time-zero history corresponding to a source history through time one. -/
def shiftInitial (x : Π _ : Iic 1, ι) : Π _ : Iic 0, ι :=
  fun _ => x ⟨1, mem_Iic.mpr le_rfl⟩

omit [Fintype ι] [DecidableEq ι] in
@[simp]
theorem shiftHistory_zero (x : Π _ : Iic 1, ι) :
    shiftHistory 0 x = shiftInitial x := by
  funext k
  have hk : k = (⟨0, mem_Iic.mpr le_rfl⟩ : Iic 0) := Subsingleton.elim _ _
  subst k
  rfl

/-- Zero-horizon base case of shift covariance for the production trajectory
kernel. -/
theorem finiteTrajectoryKernel_shift_covariant_zero
    (P : Matrix ι ι ℝ) (hP : P ∈ Matrix.rowStochastic ℝ ι)
    (x : Π _ : Iic 1, ι) :
    (InfoGeometry.QuantumContext.FiniteMarkovTransitionKernel.finiteTrajectoryKernel
      P hP 1 1 x).map (shiftHistory 0) =
      InfoGeometry.QuantumContext.FiniteMarkovTransitionKernel.finiteTrajectoryKernel
        P hP 0 0 (shiftInitial x) := by
  change (Measure.dirac x).map (shiftHistory 0) = Measure.dirac (shiftInitial x)
  rw [Measure.map_dirac' (by fun_prop)]
  congr 1
  exact shiftHistory_zero x

end InfoGeometry.QuantumContext.FiniteMarkovTrajectoryShiftCovariance
