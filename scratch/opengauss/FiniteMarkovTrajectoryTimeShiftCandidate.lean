/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.QuantumContext.FiniteMarkovTransitionKernel
import Mathlib.Probability.Kernel.IonescuTulcea.PartialTraj

/-!
# Coordinate transport for a one-time-shifted Markov continuation

This file proves the carrier-level reindexing needed to compare a continuation
from a history through time one with a zero-start successor path. It does not
claim equality of the corresponding probability measures at arbitrary horizon.
-/

noncomputable section

namespace InfoGeometry.QuantumContext.FiniteMarkovTrajectoryTimeShiftCandidate

open MeasureTheory ProbabilityTheory Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

local instance : MeasurableSpace ι := ⊤
local instance : MeasurableSingletonClass ι := inferInstance

/-- States at times `2, …, n + 1` in a continuation history through `n + 1`. -/
def continuationCoordinates (n : ℕ) :
    (Π _ : Iic (n + 1), ι) → Fin n → ι := fun x k =>
      x ⟨k.val + 2, mem_Iic.mpr (by have hk := k.isLt; omega)⟩

/-- Reindex a history through `n + 1` as a history through `1 + n`.
The equality of these bounds is arithmetic; the coordinate values are retained. -/
def castHistoryBounds (n : ℕ) :
    (Π _ : Iic (n + 1), ι) → Π _ : Iic (1 + n), ι := fun x k =>
      x ⟨k.val, mem_Iic.mpr (by have hk := mem_Iic.mp k.2; omega)⟩

omit [Fintype ι] [DecidableEq ι] in
/-- The suffix coordinates of the reindexed history are exactly its states
at times `2, …, n + 1`. This is the explicit dependent-index transport used
after `partialTraj_eq_prod` isolates the `Ioc 1 (1+n)` block. -/
theorem continuationCoordinates_eq_suffixCoordinates (n : ℕ)
    (x : Π _ : Iic (n + 1), ι) :
    continuationCoordinates n x =
      (fun y : Π _ : Ioc 1 (1 + n), ι =>
        fun k : Fin n =>
          y ⟨1 + k.val + 1, mem_Ioc.mpr ⟨by omega,
            by have hk := k.isLt; omega⟩⟩)
        (restrict₂ (π := fun _ : ℕ => ι)
          (Ioc_subset_Iic_self (a := 1) (b := 1 + n))
          (castHistoryBounds n x)) := by
  funext k
  simp only [continuationCoordinates, castHistoryBounds, restrict₂]
  congr 1
  apply Subtype.ext
  simp
  omega

end InfoGeometry.QuantumContext.FiniteMarkovTrajectoryTimeShiftCandidate
end
