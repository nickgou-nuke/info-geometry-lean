/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.QuantumContext.FiniteMarkovTransitionKernel
import Mathlib.Probability.Kernel.IonescuTulcea.PartialTraj

/-!
# Typed horizon-one singleton evaluation for finite Markov trajectories
-/

noncomputable section

namespace InfoGeometry.QuantumContext.FiniteMarkovPartialTrajSingletonEvalTyped

open MeasureTheory ProbabilityTheory MeasurableEquiv
open scoped ENNReal
open InfoGeometry.QuantumContext.FiniteMarkovTransitionKernel

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

local instance : MeasurableSpace ι := ⊤
local instance : MeasurableSingletonClass ι := inferInstance

private abbrev segmentEquiv : ι ≃ᵐ (Π _ : Finset.Ioc 0 1, ι) :=
  MeasurableEquiv.piSingleton (X := fun _ : ℕ => ι) 0

/-- The horizon-one trajectory kernel assigns the matrix transition mass to a
history with the specified initial coordinate. -/
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
      Π _ : Finset.Iic 1, ι := _root_.IicProdIoc (X := fun _ : ℕ => ι) 0 1
  have hglue (j : ι) : glue (initial, segmentEquiv j) = x ↔
      j = x ⟨1, Finset.mem_Iic.mpr (by omega)⟩ := by
    constructor
    · intro h
      have hlast := congrFun h ⟨1, Finset.mem_Iic.mpr (by omega)⟩
      simpa [glue, initial, _root_.IicProdIoc, segmentEquiv] using hlast.symm
    · intro hj
      funext t
      have htle : t.val ≤ 1 := t.property
      have ht : t.val = 0 ∨ t.val = 1 := by omega
      rcases ht with ht | ht
      · have hcoord : t = ⟨0, Finset.mem_Iic.mpr (by omega)⟩ := Subtype.ext ht
        rw [hcoord]
        simpa [glue, initial, _root_.IicProdIoc] using hstart.symm
      · have hcoord : t = ⟨1, Finset.mem_Iic.mpr (by omega)⟩ := Subtype.ext ht
        rw [hcoord]
        simp [glue, initial, _root_.IicProdIoc, segmentEquiv, hj]
  have hpre : (fun j : ι => glue (initial, segmentEquiv j) = x) =
      ({x ⟨1, Finset.mem_Iic.mpr (by omega)⟩} : Set ι) := by
    ext j
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
    exact hglue j
  change (Kernel.partialTraj (historyTransitionKernel P hP) 0 1) initial
      ({x} : Set (Π _ : Finset.Iic 1, ι)) = _
  rw [Kernel.partialTraj_succ_self]
  rw [Kernel.map_apply' _ (by fun_prop) initial (MeasurableSet.singleton x)]
  rw [Kernel.id_prod_apply' _ initial
    (MeasurableSet.preimage (by fun_prop) (MeasurableSet.singleton x))]
  rw [Kernel.map_apply' _ segmentEquiv.measurable initial
    (MeasurableSet.preimage (by fun_prop)
      (MeasurableSet.preimage (by fun_prop) (MeasurableSet.singleton x)))]
  rw [hpre]
  simp [historyTransitionKernel, Kernel.comp_apply, Kernel.deterministic_apply,
    transitionKernel_singleton]

end InfoGeometry.QuantumContext.FiniteMarkovPartialTrajSingletonEvalTyped
