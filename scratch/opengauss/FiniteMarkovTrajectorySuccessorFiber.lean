/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import scratch.opengauss.FiniteMarkovTrajectoryFullLawCandidate
import scratch.opengauss.FiniteMarkovSuccessorPathMass

/-!
# Fixed-initial-state fiber of the successor-coordinate map

This scratch lemma identifies the history fiber over a successor path once
the time-zero coordinate is fixed. It is the finite-carrier measure step
needed to reduce the full pushforward law to singleton masses.
-/

noncomputable section

namespace InfoGeometry.QuantumContext.FiniteMarkovTrajectorySuccessorFiber

open MeasureTheory ProbabilityTheory
open InfoGeometry.QuantumContext.FiniteMarkovTransitionKernel
open InfoGeometry.QuantumContext.FiniteMarkovTrajectoryFullLawCandidate
open InfoGeometry.QuantumContext.FiniteMarkovSuccessorPathMass

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

local instance : MeasurableSpace ι := ⊤
local instance : MeasurableSingletonClass ι := inferInstance
local instance (n : ℕ) : MeasurableSpace (Fin n → ι) := ⊤
local instance (n : ℕ) : MeasurableSingletonClass (Fin n → ι) := inferInstance
local instance (n : ℕ) : MeasurableSpace (Π _ : Finset.Iic n, ι) := ⊤
local instance (n : ℕ) : MeasurableSingletonClass (Π _ : Finset.Iic n, ι) := inferInstance

/-- The history obtained by adjoining the fixed initial state to a successor
path. -/
def historyOfSuccessors (n : ℕ) (i : ι) (p : Fin n → ι) :
    Π _ : Finset.Iic n, ι := fun t =>
  if ht : t.1 = 0 then i else p ⟨t.1 - 1, by
    have ht' := Finset.mem_Iic.mp t.2
    have hp : t.1 - 1 < n := by omega
    exact hp⟩

/-- Successor extraction recovers the path used to construct the history. -/
theorem trajectorySuccessors_historyOfSuccessors (n : ℕ) (i : ι)
    (p : Fin n → ι) :
    trajectorySuccessors n (historyOfSuccessors n i p) = p := by
  funext k
  simp only [trajectorySuccessors, historyOfSuccessors]
  have hk : k.val + 1 ≠ 0 := by omega
  simp only [dif_neg hk]
  congr 1

/-- With its initial coordinate fixed, a history is uniquely determined by
all successor coordinates. -/
theorem history_ext_of_successors {n : ℕ} (i : ι)
    (x y : Π _ : Finset.Iic n, ι)
    (hx : x ⟨0, Finset.mem_Iic.mpr (Nat.zero_le n)⟩ = i)
    (hy : y ⟨0, Finset.mem_Iic.mpr (Nat.zero_le n)⟩ = i)
    (hxy : trajectorySuccessors n x = trajectorySuccessors n y) : x = y := by
  funext t
  by_cases ht : t.1 = 0
  · have ht0 : t = ⟨0, Finset.mem_Iic.mpr (Nat.zero_le n)⟩ := Subtype.ext ht
    rw [ht0, hx, hy]
  · have htpos : 0 < t.1 := Nat.pos_of_ne_zero ht
    have htle : t.1 ≤ n := Finset.mem_Iic.mp t.2
    let k : Fin n := ⟨t.1 - 1, by omega⟩
    have hcoord : t = ⟨k.val + 1, Finset.mem_Iic.mpr (by
        omega)⟩ := by
      apply Subtype.ext
      change t.1 = k.val + 1
      simp [k]
      omega
    rw [hcoord]
    have hval := congrFun hxy k
    exact hval

/-- Exact singleton fiber of successor extraction over histories whose
time-zero coordinate is fixed. -/
theorem successorFiber_eq_singleton {n : ℕ} (i : ι) (p : Fin n → ι) :
    {x : Π _ : Finset.Iic n, ι | x ⟨0, Finset.mem_Iic.mpr (Nat.zero_le n)⟩ = i ∧
      trajectorySuccessors n x = p} = {historyOfSuccessors n i p} := by
  ext x
  constructor
  · rintro ⟨h0, hpath⟩
    have hEq := history_ext_of_successors i x
      (historyOfSuccessors n i p) h0 (by simp [historyOfSuccessors])
      (hpath.trans (trajectorySuccessors_historyOfSuccessors n i p).symm)
    simp [hEq]
  · intro hx
    have hx' : x = historyOfSuccessors n i p := by simpa using hx
    subst x
    exact ⟨by simp [historyOfSuccessors], trajectorySuccessors_historyOfSuccessors n i p⟩

end InfoGeometry.QuantumContext.FiniteMarkovTrajectorySuccessorFiber
end
