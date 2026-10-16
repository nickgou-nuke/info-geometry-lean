/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.QuantumContext.FiniteMarkovTransitionKernel
import Mathlib.Probability.Kernel.IonescuTulcea.PartialTraj

/-!
# Singleton fiber for a one-step finite trajectory extension

This leaf evaluates the final `partialTraj` map on a singleton by reducing it
to the fiber in the old-history / successor-block product. It deliberately
isolates that fiber before attempting a horizon induction.
-/

noncomputable section

namespace InfoGeometry.QuantumContext.FiniteMarkovTrajectorySingletonFiber

open MeasureTheory ProbabilityTheory
open scoped ENNReal

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

local instance : MeasurableSpace ι := ⊤
local instance : MeasurableSingletonClass ι := inferInstance

/-- A one-step extension assigns to a target singleton the transition-block
kernel evaluated on the exact fiber of the gluing map over that target. -/
theorem finiteTrajectoryKernel_succ_singleton_fiber
    (P : Matrix ι ι ℝ) (hP : P ∈ Matrix.rowStochastic ℝ ι) (n : ℕ)
    (h : Π _ : Finset.Iic n, ι) (x : Π _ : Finset.Iic (n + 1), ι) :
    FiniteMarkovTransitionKernel.finiteTrajectoryKernel P hP n (n + 1) h {x} =
      (((Kernel.id ×ₖ
        (FiniteMarkovTransitionKernel.historyTransitionKernel P hP n).map
          (MeasurableEquiv.piSingleton (X := fun _ : ℕ => ι) n)) h)
        ((_root_.IicProdIoc (X := fun _ : ℕ => ι) n (n + 1)) ⁻¹' {x})) := by
  classical
  rw [FiniteMarkovTransitionKernel.finiteTrajectoryKernel,
    Kernel.partialTraj_succ_self]
  rw [Kernel.map_apply' _ (by fun_prop) h (MeasurableSet.singleton x)]

/-- Explicitly, the one-step law contributes the suffix singleton precisely
when the old-history component of the target history is the supplied history.
This is the fiber calculation used by a last-step singleton induction. -/
theorem finiteTrajectoryKernel_succ_singleton_split
    (P : Matrix ι ι ℝ) (hP : P ∈ Matrix.rowStochastic ℝ ι) (n : ℕ)
    (h : Π _ : Finset.Iic n, ι) (x : Π _ : Finset.Iic (n + 1), ι) :
    FiniteMarkovTransitionKernel.finiteTrajectoryKernel P hP n (n + 1) h {x} =
      if ((MeasurableEquiv.IicProdIoc (X := fun _ : ℕ => ι) (Nat.le_succ n)).symm x).1 = h
      then
        (((FiniteMarkovTransitionKernel.historyTransitionKernel P hP n).map
          (MeasurableEquiv.piSingleton (X := fun _ : ℕ => ι) n)) h)
          {((MeasurableEquiv.IicProdIoc (X := fun _ : ℕ => ι) (Nat.le_succ n)).symm x).2}
      else 0 := by
  classical
  let e := MeasurableEquiv.IicProdIoc (X := fun _ : ℕ => ι) (Nat.le_succ n)
  have hglue : (_root_.IicProdIoc (X := fun _ : ℕ => ι) n (n + 1)) = e := by
    exact MeasurableEquiv.coe_IicProdIoc (X := fun _ : ℕ => ι) (Nat.le_succ n)
  have hfiber :
      {s : Π _ : Finset.Ioc n (n + 1), ι |
        _root_.IicProdIoc (X := fun _ : ℕ => ι) n (n + 1) (h, s) = x} =
      if (e.symm x).1 = h then {(e.symm x).2} else ∅ := by
    ext s
    rw [hglue]
    by_cases hp : (e.symm x).1 = h
    · simp only [Set.mem_setOf_eq, hp, if_pos, Set.mem_singleton_iff]
      constructor
      · intro hx
        have heq : (h, s) = e.symm x :=
          e.injective (hx.trans (e.apply_symm_apply x).symm)
        exact congrArg Prod.snd heq
      · intro hs
        have heq : (h, s) = e.symm x := Prod.ext hp.symm hs
        rw [heq]
        exact e.apply_symm_apply x
    · simp only [Set.mem_setOf_eq, hp, if_neg, Set.mem_empty_iff_false]
      constructor
      · intro hx
        have heq : (h, s) = e.symm x :=
          e.injective (hx.trans (e.apply_symm_apply x).symm)
        exact hp (congrArg Prod.fst heq).symm
      · intro hs
        exact False.elim hs
  rw [finiteTrajectoryKernel_succ_singleton_fiber]
  rw [Kernel.id_prod_apply' _ h
    ((MeasurableSet.singleton x).preimage
      (by fun_prop : Measurable
        (_root_.IicProdIoc (X := fun _ : ℕ => ι) n (n + 1))))]
  change ((FiniteMarkovTransitionKernel.historyTransitionKernel P hP n).map
    (MeasurableEquiv.piSingleton (X := fun _ : ℕ => ι) n) h)
    ({s : Π _ : Finset.Ioc n (n + 1), ι |
      _root_.IicProdIoc (X := fun _ : ℕ => ι) n (n + 1) (h, s) = x}) = _
  rw [hfiber]
  split_ifs <;> simp [e]

end InfoGeometry.QuantumContext.FiniteMarkovTrajectorySingletonFiber
