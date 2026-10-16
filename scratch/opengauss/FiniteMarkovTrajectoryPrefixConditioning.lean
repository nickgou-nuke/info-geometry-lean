/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.QuantumContext.FiniteMarkovTransitionKernel
import InfoGeometry.QuantumContext.FiniteMarkovHittingPMFExpectation

/-!
# Prefix preservation and first-step coordinates for finite trajectories

This scratch owner develops the general-start-time leaves needed to assemble
the all-horizon path-law theorem. The trajectory kernel preserves its input
prefix exactly, and successor coordinates split as a `Fin.cons` of the first
step and the remaining successor coordinates. Together with the staged PMF
bind leaf, the remaining step is to transport the continuation pushforward
through the conditional kernel using this fixed-prefix fact.
-/

noncomputable section

namespace InfoGeometry.QuantumContext.FiniteMarkovTrajectoryPrefixConditioning

open MeasureTheory ProbabilityTheory
open Preorder
open scoped ENNReal
open InfoGeometry.QuantumContext.FiniteMarkovTransitionKernel
open InfoGeometry.QuantumContext.FiniteMarkovHittingPMFExpectation

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

local instance : MeasurableSpace ι := ⊤
local instance : MeasurableSingletonClass ι := inferInstance

/-- On an individual input history, the trajectory output retains the whole
initial prefix with Dirac probability. -/
theorem partialTraj_output_prefix_is_dirac
    (P : Matrix ι ι ℝ) (hP : P ∈ Matrix.rowStochastic ℝ ι)
    (a b : ℕ) (hab : a ≤ b) (h : Π _ : Finset.Iic a, ι) :
    Measure.map (Preorder.frestrictLe₂ (π := fun _ : ℕ => ι) hab)
      (Kernel.partialTraj (X := fun _ : ℕ => ι)
        (historyTransitionKernel P hP) a b h) = Measure.dirac h := by
  rw [Kernel.partialTraj_map_frestrictLe₂_apply
    (X := fun _ : ℕ => ι) (κ := historyTransitionKernel P hP) h
    (a := a) (b := a) (c := b) hab]
  simp only [Kernel.partialTraj_self, Kernel.id_apply]

/-- Successor-coordinate extraction from a trajectory beginning at time `a`.
The `k`th coordinate is the state at time `a + k + 1`. -/
def successorCoordinates (a n : ℕ) :
    (Π _ : Finset.Iic (a + n), ι) → Fin n → ι :=
  fun x k => x ⟨a + k.val + 1,
    Finset.mem_Iic.mpr (by have hk := k.isLt; omega)⟩

/-- First-step decomposition of successor coordinates, valid at every start
time. -/
theorem successorCoordinates_succ_eq_cons (a n : ℕ)
    (x : Π _ : Finset.Iic (a + (n + 1)), ι) :
    successorCoordinates a (n + 1) x =
      @Fin.cons n (fun _ => ι)
        (x ⟨a + 1, Finset.mem_Iic.mpr (by omega)⟩)
        (successorCoordinates (a + 1) n (by
          exact fun t => x ⟨t.val, Finset.mem_Iic.mpr (by
            have ht : t.val ≤ (a + 1) + n := Finset.mem_Iic.mp t.2
            omega)⟩)) := by
  funext k
  refine Fin.cases ?_ ?_ k
  · rfl
  · intro k
    simp only [Fin.cons_succ, successorCoordinates]
    congr 1
    apply Subtype.ext
    simp
    omega

/-- The generic kernel composition law split immediately after the first
transition from time `a` to time `a + 1`. -/
theorem finiteTrajectoryKernel_split_after_first_transition
    (P : Matrix ι ι ℝ) (hP : P ∈ Matrix.rowStochastic ℝ ι)
    (a n : ℕ) :
    finiteTrajectoryKernel P hP (a + 1) (a + (n + 1)) ∘ₖ
        finiteTrajectoryKernel P hP a (a + 1) =
      finiteTrajectoryKernel P hP a (a + (n + 1)) := by
  exact finiteTrajectoryKernel_comp P hP
    (a := a) (b := a + 1) (c := a + (n + 1))
    (by omega) (by omega)

end InfoGeometry.QuantumContext.FiniteMarkovTrajectoryPrefixConditioning
end
