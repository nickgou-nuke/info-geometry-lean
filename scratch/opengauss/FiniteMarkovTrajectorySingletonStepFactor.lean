/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.QuantumContext.FiniteMarkovTransitionKernel
import Mathlib.Probability.Kernel.IonescuTulcea.PartialTraj

/-!
# Singleton transition factor for a finite trajectory extension

This leaf evaluates the singleton mass contributed by one final transition,
provided the output history extends the supplied prefix. It is the local
factor required by a horizon induction for the full path product formula.
-/

noncomputable section

namespace InfoGeometry.QuantumContext.FiniteMarkovTrajectorySingletonStepFactor

open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

local instance : MeasurableSpace ι := ⊤
local instance : MeasurableSingletonClass ι := inferInstance

open InfoGeometry.QuantumContext.FiniteMarkovTransitionKernel

/-- A target history's last coordinate. -/
def finalState (n : ℕ) (x : Π _ : Iic (n + 1), ι) : ι :=
  x ⟨n + 1, mem_Iic.mpr le_rfl⟩

/-- A target history's prefix through time `n`. -/
def prefixState (n : ℕ) (x : Π _ : Iic (n + 1), ι) : Π _ : Iic n, ι :=
  fun k => x ⟨k.1, Iic_subset_Iic.mpr (Nat.le_succ n) k.2⟩

/-- Singleton fiber for the last partial-trajectory extension. -/
private theorem finiteTrajectoryKernel_succ_singleton_fiber
    (P : Matrix ι ι ℝ) (hP : P ∈ Matrix.rowStochastic ℝ ι) (n : ℕ)
    (h : Π _ : Iic n, ι) (x : Π _ : Iic (n + 1), ι) :
    finiteTrajectoryKernel P hP n (n + 1) h {x} =
      (((Kernel.id ×ₖ (historyTransitionKernel P hP n).map
        (MeasurableEquiv.piSingleton (X := fun _ : ℕ => ι) n)) h)
        ((_root_.IicProdIoc (X := fun _ : ℕ => ι) n (n + 1)) ⁻¹' {x})) := by
  classical
  rw [finiteTrajectoryKernel, Kernel.partialTraj_succ_self]
  rw [Kernel.map_apply' _ (by fun_prop) h (MeasurableSet.singleton x)]

/-- The one-step singleton fiber separates a fixed prefix from its successor
block. -/
theorem trajectoryKernel_succ_singleton_split
    (P : Matrix ι ι ℝ) (hP : P ∈ Matrix.rowStochastic ℝ ι) (n : ℕ)
    (h : Π _ : Iic n, ι) (x : Π _ : Iic (n + 1), ι) :
    finiteTrajectoryKernel P hP n (n + 1) h {x} =
      if ((MeasurableEquiv.IicProdIoc (X := fun _ : ℕ => ι)
          (Nat.le_succ n)).symm x).1 = h then
        (((historyTransitionKernel P hP n).map
          (MeasurableEquiv.piSingleton (X := fun _ : ℕ => ι) n)) h)
          {((MeasurableEquiv.IicProdIoc (X := fun _ : ℕ => ι)
            (Nat.le_succ n)).symm x).2}
      else 0 := by
  classical
  let e := MeasurableEquiv.IicProdIoc (X := fun _ : ℕ => ι) (Nat.le_succ n)
  have hglue : (_root_.IicProdIoc (X := fun _ : ℕ => ι) n (n + 1)) = e := by
    exact MeasurableEquiv.coe_IicProdIoc (X := fun _ : ℕ => ι) (Nat.le_succ n)
  have hfiber :
      {s : Π _ : Ioc n (n + 1), ι |
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
  change ((historyTransitionKernel P hP n).map
    (MeasurableEquiv.piSingleton (X := fun _ : ℕ => ι) n) h)
    ({s : Π _ : Ioc n (n + 1), ι |
      _root_.IicProdIoc (X := fun _ : ℕ => ι) n (n + 1) (h, s) = x}) = _
  rw [hfiber]
  split_ifs <;> simp [e]

/-- For a compatible prefix, one `partialTraj` step assigns exactly the
transition probability from the prefix endpoint to the target's last state.
This is the singleton-mass induction step, independent of any horizon
recursion for the preceding prefix law. -/
theorem finiteTrajectoryKernel_succ_singleton_factor
    (P : Matrix ι ι ℝ) (hP : P ∈ Matrix.rowStochastic ℝ ι) (n : ℕ)
    (h : Π _ : Iic n, ι) (x : Π _ : Iic (n + 1), ι)
    (hprefix : prefixState n x = h) :
    finiteTrajectoryKernel P hP n (n + 1) h {x} =
      ENNReal.ofReal (P (h ⟨n, mem_Iic.mpr le_rfl⟩) (finalState n x)) := by
  classical
  let e := MeasurableEquiv.IicProdIoc (X := fun _ : ℕ => ι) (Nat.le_succ n)
  have hprefix' : (e.symm x).1 = h := by
    have hfst : (e.symm x).1 = prefixState n x := by
      funext k
      simp [e, prefixState, MeasurableEquiv.IicProdIoc]
    exact hfst.trans hprefix
  have hsplit := congrArg (fun κ => κ h)
    (finiteTrajectoryKernel_succ_endpoint P hP n)
  have hsingleton := historyTransitionKernel_piSingleton_singleton
    P hP n h (finalState n x)
  have hsuffix : (e.symm x).2 =
      MeasurableEquiv.piSingleton (X := fun _ : ℕ => ι) n (finalState n x) := by
    funext k
    have hk : k.1 = n + 1 := by
      have hk' := k.2
      simp only [mem_Ioc] at hk'
      omega
    have hkEq : k = ⟨n + 1, right_mem_Ioc.mpr (Nat.lt_succ_self n)⟩ :=
      Subtype.ext hk
    subst k
    simp [e, MeasurableEquiv.IicProdIoc, MeasurableEquiv.piSingleton,
      finalState]
  rw [trajectoryKernel_succ_singleton_split P hP n h x]
  have hp : ((MeasurableEquiv.IicProdIoc (X := fun _ : ℕ => ι)
      (Nat.le_succ n)).symm x).1 = h := by
    simpa [e] using hprefix'
  rw [if_pos hp]
  rw [hsuffix]
  exact hsingleton

end InfoGeometry.QuantumContext.FiniteMarkovTrajectorySingletonStepFactor
end
