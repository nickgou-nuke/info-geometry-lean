/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.QuantumContext.FiniteMarkovTransitionKernel

/-!
# One-step successor law at an arbitrary starting time

This leaf removes the time-zero restriction from the production one-step
successor law. It is the base case needed by a time-shifted continuation
induction; it does not assert the arbitrary-horizon continuation law.
-/

noncomputable section

namespace InfoGeometry.QuantumContext.FiniteMarkovTrajectoryArbitraryStartOneStep

open MeasureTheory ProbabilityTheory

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

local instance : MeasurableSpace ι := ⊤
local instance : MeasurableSingletonClass ι := inferInstance
local instance : MeasurableSpace (Fin 1 → ι) := ⊤
local instance : MeasurableSingletonClass (Fin 1 → ι) := inferInstance

open InfoGeometry.QuantumContext.FiniteMarkovTransitionKernel

/-- The sole successor coordinate of a one-step history beginning at time
`a`. -/
def oneSuccessorCoordinate (a : ℕ) :
    (Π _ : Finset.Iic (a + 1), ι) → Fin 1 → ι := fun x _ =>
      x ⟨a + 1, Finset.mem_Iic.mpr le_rfl⟩

/-- At every start time and every fixed source history, the one-step
trajectory law pushed to its sole successor coordinate is the row PMF at the
source endpoint, embedded as a constant one-coordinate path. -/
theorem finiteTrajectoryKernel_arbitraryStart_oneStep_successor_law
    (P : Matrix ι ι ℝ) (hP : P ∈ Matrix.rowStochastic ℝ ι)
    (a : ℕ) (h : Π _ : Finset.Iic a, ι) :
    (finiteTrajectoryKernel P hP a (a + 1) h).map
        (oneSuccessorCoordinate (ι := ι) a) =
      ((rowPMF P hP (h ⟨a, Finset.mem_Iic.mpr le_rfl⟩)).map
        (fun j : ι => fun _ : Fin 1 => j)).toMeasure := by
  let endpoint : (Π _ : Finset.Iic (a + 1), ι) → ι :=
    fun x => x ⟨a + 1, Finset.mem_Iic.mpr le_rfl⟩
  let embed : ι → Fin 1 → ι := fun j _ => j
  have he := congrArg (fun κ => κ h)
    (finiteTrajectoryKernel_succ_endpoint P hP a)
  rw [Kernel.map_apply _ (by fun_prop) h] at he
  have hcoord : oneSuccessorCoordinate (ι := ι) a = embed ∘ endpoint := by
    funext x k
    fin_cases k
    rfl
  rw [hcoord, ← Measure.map_map (by fun_prop) (by fun_prop), he]
  simp only [historyTransitionKernel, Kernel.comp_apply,
    Kernel.deterministic_apply, transitionKernel]
  rw [Measure.dirac_bind (by fun_prop)
    (h ⟨a, Finset.mem_Iic.mpr le_rfl⟩)]
  exact PMF.toMeasure_map
    (rowPMF P hP (h ⟨a, Finset.mem_Iic.mpr le_rfl⟩))
    (f := embed) (by fun_prop)

end InfoGeometry.QuantumContext.FiniteMarkovTrajectoryArbitraryStartOneStep
end
