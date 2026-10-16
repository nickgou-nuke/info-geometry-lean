/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.QuantumContext.FiniteMarkovTransitionKernel
import Mathlib.Probability.Kernel.Composition.MapComap
import Mathlib.Probability.Kernel.IonescuTulcea.Maps

/-!
# One-step fiber leaf for the finite Markov trajectory law

Pushing the history transition kernel to its singleton successor-coordinate
carrier preserves the one-step transition probability.
-/

noncomputable section

namespace InfoGeometry.QuantumContext.FiniteMarkovTrajectoryOneStepFiberLeaf

open MeasureTheory ProbabilityTheory
open scoped ENNReal

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

local instance : MeasurableSpace ι := ⊤
local instance : MeasurableSingletonClass ι := inferInstance

/-- The one-step successor fiber over a history is exactly its transition
probability to the selected state. `piSingleton n` identifies the final
interval `Ioc n (n+1)` with its unique coordinate. -/
theorem historyTransitionKernel_piSingleton_singleton
    (P : Matrix ι ι ℝ) (hP : P ∈ Matrix.rowStochastic ℝ ι)
    (n : ℕ) (h : Π _ : Finset.Iic n, ι) (y : ι) :
    ((FiniteMarkovTransitionKernel.historyTransitionKernel P hP n).map
      (MeasurableEquiv.piSingleton (X := fun _ : ℕ => ι) n)) h
      ({MeasurableEquiv.piSingleton (X := fun _ : ℕ => ι) n y} :
        Set (Π _ : Finset.Ioc n (n + 1), ι)) =
      ENNReal.ofReal (P (h ⟨n, Finset.mem_Iic.mpr le_rfl⟩) y) := by
  have hf : Measurable
      (MeasurableEquiv.piSingleton (X := fun _ : ℕ => ι) n) :=
    (MeasurableEquiv.piSingleton (X := fun _ : ℕ => ι) n).measurable
  have hs : MeasurableSet
      ({MeasurableEquiv.piSingleton (X := fun _ : ℕ => ι) n y} :
        Set (Π _ : Finset.Ioc n (n + 1), ι)) := MeasurableSet.singleton _
  rw [Kernel.map_apply' _ hf h hs]
  simp only [FiniteMarkovTransitionKernel.historyTransitionKernel,
    Kernel.comp_apply, Kernel.deterministic_apply]
  rw [Measure.dirac_bind (by fun_prop)
    (h ⟨n, Finset.mem_Iic.mpr le_rfl⟩)]
  have hpre :
      (MeasurableEquiv.piSingleton (X := fun _ : ℕ => ι) n) ⁻¹'
        {MeasurableEquiv.piSingleton (X := fun _ : ℕ => ι) n y} = {y} := by
    ext z
    simp
  rw [hpre]
  exact FiniteMarkovTransitionKernel.transitionKernel_singleton P hP _ _

end InfoGeometry.QuantumContext.FiniteMarkovTrajectoryOneStepFiberLeaf
