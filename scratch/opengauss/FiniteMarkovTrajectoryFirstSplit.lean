/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.QuantumContext.FiniteMarkovTransitionKernel
import InfoGeometry.QuantumContext.FiniteMarkovHittingPMFExpectation
import Mathlib.Probability.Kernel.Composition.CompMap

/-!
# First-transition decomposition for finite Markov trajectory laws

This scratch owner isolates the first transition in a finite trajectory
kernel. It is a structural step toward identifying the trajectory pushforward
with the recursively bound successor-path PMF.
-/

noncomputable section

namespace InfoGeometry.QuantumContext.FiniteMarkovTrajectoryFirstSplit

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open InfoGeometry.QuantumContext.FiniteMarkovTransitionKernel
open InfoGeometry.QuantumContext.FiniteMarkovHittingPMFExpectation

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

local instance : MeasurableSpace ι := ⊤
local instance : MeasurableSingletonClass ι := inferInstance

/-- Extract the successor states at times `1, …, n` from a history ending at
time `n`. -/
def trajectorySuccessors (n : ℕ) : (Π _ : Finset.Iic n, ι) → Fin n → ι :=
  fun x k => x ⟨k.val + 1,
    Finset.mem_Iic.mpr (Nat.succ_le_of_lt k.isLt)⟩

/-- The successor-coordinate extraction is measurable for the finite product
measurable structures. -/
theorem trajectorySuccessors_measurable (n : ℕ) :
    Measurable (trajectorySuccessors (ι := ι) n) := by
  fun_prop

/-- The production finite trajectory kernel splits after its first transition.
The first kernel moves from time zero to time one; the second continues from
that history through time `n + 1`. -/
theorem finiteTrajectoryKernel_first_transition_split
    (P : Matrix ι ι ℝ) (hP : P ∈ Matrix.rowStochastic ℝ ι) (n : ℕ) :
    finiteTrajectoryKernel P hP 1 (n + 1) ∘ₖ
        finiteTrajectoryKernel P hP 0 1 =
      finiteTrajectoryKernel P hP 0 (n + 1) := by
  exact finiteTrajectoryKernel_comp P hP (a := 0) (b := 1) (c := n + 1)
    zero_le (by omega)

/-- Pushing the complete trajectory through its successor-coordinate map
commutes with the first-transition kernel split. This is the exact bind-shaped
equation needed for induction on the first sampled state. -/
theorem finiteTrajectoryKernel_first_transition_pushforward_split
    (P : Matrix ι ι ℝ) (hP : P ∈ Matrix.rowStochastic ℝ ι) (n : ℕ) :
    (finiteTrajectoryKernel P hP 0 (n + 1)).map
        (trajectorySuccessors (ι := ι) (n + 1)) =
      (finiteTrajectoryKernel P hP 1 (n + 1)).map
          (trajectorySuccessors (ι := ι) (n + 1)) ∘ₖ
        finiteTrajectoryKernel P hP 0 1 := by
  rw [← finiteTrajectoryKernel_first_transition_split P hP n]
  exact Kernel.map_comp
    (finiteTrajectoryKernel P hP 0 1)
    (finiteTrajectoryKernel P hP 1 (n + 1))
    (trajectorySuccessors (ι := ι) (n + 1))

/-- Applying the first-transition pushforward split to the fixed initial
history gives an explicit conditional-law decomposition. -/
theorem finiteTrajectoryKernel_first_transition_at_initial
    (P : Matrix ι ι ℝ) (hP : P ∈ Matrix.rowStochastic ℝ ι) (n : ℕ) (i : ι) :
    ((finiteTrajectoryKernel P hP 0 (n + 1) (fun _ => i)).map
        (trajectorySuccessors (ι := ι) (n + 1))) =
      ((finiteTrajectoryKernel P hP 1 (n + 1)).map
          (trajectorySuccessors (ι := ι) (n + 1)) ∘ₖ
        finiteTrajectoryKernel P hP 0 1) (fun _ => i) := by
  have hs := congrArg
    (fun κ : Kernel (Π _ : Finset.Iic 0, ι) (Fin (n + 1) → ι) => κ (fun _ => i))
    (finiteTrajectoryKernel_first_transition_pushforward_split P hP n)
  simpa only [Kernel.map_apply _
    (trajectorySuccessors_measurable (ι := ι) (n + 1))] using hs

end InfoGeometry.QuantumContext.FiniteMarkovTrajectoryFirstSplit
end
