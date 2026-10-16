/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.QuantumContext.FiniteMarkovTransitionKernel
import Mathlib.Probability.Kernel.IonescuTulcea.PartialTraj

/-!
# Explicit horizon-one singleton evaluation for finite Markov trajectories

This candidate follows Mathlib's final-coordinate trajectory extension and
keeps both kernel-map evaluations explicit.
-/

noncomputable section

namespace InfoGeometry.QuantumContext.FiniteMarkovPartialTrajSingletonEvalExplicit

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open InfoGeometry.QuantumContext.FiniteMarkovTransitionKernel

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

local instance : MeasurableSpace ι := ⊤
local instance : MeasurableSingletonClass ι := inferInstance

/-- The final coordinate of a length-one successor segment. -/
def lastSegmentState (y : Π _ : Finset.Ioc 0 1, ι) : ι :=
  y ⟨1, Finset.mem_Ioc.mpr ⟨by omega, le_rfl⟩⟩

/-- The horizon-one trajectory kernel assigns the expected mass to a history
whose time-zero coordinate is the prescribed initial state. -/
theorem finiteTrajectoryKernel_one_singleton
    (P : Matrix ι ι ℝ) (hP : P ∈ Matrix.rowStochastic ℝ ι) (i : ι)
    (x : Π _ : Finset.Iic 1, ι)
    (hstart : x ⟨0, Finset.mem_Iic.mpr (by omega)⟩ = i) :
    finiteTrajectoryKernel P hP 0 1 (fun _ => i)
      ({x} : Set (Π _ : Finset.Iic 1, ι)) =
      ENNReal.ofReal (P i (x ⟨1, Finset.mem_Iic.mpr (by omega)⟩)) := by
  classical
  let initial : Π _ : Finset.Iic 0, ι := fun _ => i
  let glue : (Π _ : Finset.Iic 0, ι) × (Π _ : Finset.Ioc 0 1, ι) →
      Π _ : Finset.Iic 1, ι := Kernel.IicProdIoc 0 1
  have hglue (j : ι) : glue (initial, fun _ => j) = x ↔
      j = x ⟨1, Finset.mem_Iic.mpr (by omega)⟩ := by
    constructor
    · intro h
      have hlast := congrFun h ⟨1, Finset.mem_Iic.mpr (by omega)⟩
      simpa [glue, initial, Kernel.IicProdIoc] using hlast.symm
    · intro hj
      funext t
      have ht : t.val = 0 ∨ t.val = 1 := by have := t.property; omega
      rcases ht with ht | ht
      · have hcoord : t = ⟨0, Finset.mem_Iic.mpr (by omega)⟩ := by
          apply Finset.Subtype.ext
          exact ht
        rw [hcoord]
        simpa [glue, initial, Kernel.IicProdIoc] using hstart.symm
      · have hcoord : t = ⟨1, Finset.mem_Iic.mpr (by omega)⟩ := by
          apply Finset.Subtype.ext
          exact ht
        rw [hcoord]
        simp [glue, initial, Kernel.IicProdIoc, hj]
  change (Kernel.partialTraj (historyTransitionKernel P hP) 0 1) initial
      ({x} : Set (Π _ : Finset.Iic 1, ι)) = _
  rw [Kernel.partialTraj_succ_self]
  rw [Kernel.map_apply' _ (by fun_prop) initial (MeasurableSet.singleton x)]
  rw [Kernel.id_prod_apply' _ initial
    (MeasurableSet.preimage (by fun_prop) (MeasurableSet.singleton x))]
  rw [Kernel.map_apply' _ (by fun_prop) initial
    (MeasurableSet.preimage (by fun_prop)
      (MeasurableSet.preimage (by fun_prop) (MeasurableSet.singleton x)))]
  have hpre : (fun j : ι => glue (initial, fun _ => j) = x) =
      ({x ⟨1, Finset.mem_Iic.mpr (by omega)⟩} : Set ι) := by
    ext j
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
    exact hglue j
  rw [historyTransitionKernel, Kernel.comp_apply, Kernel.deterministic_apply]
  simp [hpre, lastSegmentState, transitionKernel_singleton]

end InfoGeometry.QuantumContext.FiniteMarkovPartialTrajSingletonEvalExplicit
