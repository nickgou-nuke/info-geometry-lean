/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import scratch.opengauss.FiniteMarkovTrajectoryFullLawCandidate
import scratch.opengauss.FiniteMarkovTrajectoryPrefixConditioning
import scratch.opengauss.FiniteMarkovTrajectorySingletonRecurrence
import scratch.opengauss.FiniteMarkovTrajectorySuccessorFiber
import scratch.opengauss.FiniteMarkovSuccessorPathMass

/-!
# Full finite-horizon successor-path law candidate

This file assembles the fixed-start fiber, prefix preservation, singleton
recurrence, and path-PMF product formula. Any theorem here is kernel-checked;
the owner theorem is included only when the complete measure identity closes.
-/

noncomputable section

namespace InfoGeometry.QuantumContext.FiniteMarkovTrajectoryFullSuccessorLaw

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
open InfoGeometry.QuantumContext.FiniteMarkovTransitionKernel
open InfoGeometry.QuantumContext.FiniteMarkovHittingPMFExpectation
open InfoGeometry.QuantumContext.FiniteMarkovTrajectoryFullLawCandidate
open InfoGeometry.QuantumContext.FiniteMarkovTrajectoryPrefixConditioning
open InfoGeometry.QuantumContext.FiniteMarkovTrajectorySingletonStepFactor
open InfoGeometry.QuantumContext.FiniteMarkovTrajectorySuccessorFiber
open InfoGeometry.QuantumContext.FiniteMarkovSuccessorPathMass

variable {ι : Type*}

local instance : MeasurableSpace ι := ⊤
local instance : MeasurableSingletonClass ι := inferInstance

/-- The time-zero coordinate of a finite trajectory history. -/
def trajectoryInitial (n : ℕ) (x : Π _ : Finset.Iic n, ι) : ι :=
  x ⟨0, Finset.mem_Iic.mpr (Nat.zero_le n)⟩

private theorem stateAt_prefix_castSucc {n : ℕ} (i : ι)
    (p : Fin (n + 1) → ι) (k : Fin n) :
    stateAt i (fun j => p j.castSucc) k.castSucc =
      stateAt i p k.castSucc.castSucc := by
  cases n with
  | zero => exact Fin.elim0 k
  | succ n =>
      refine Fin.cases ?_ ?_ k
      · rfl
      · intro k
        simp [stateAt]

private theorem stateAt_prefix_succ {n : ℕ} (i : ι)
    (p : Fin (n + 1) → ι) (k : Fin n) :
    stateAt i (fun j => p j.castSucc) k.succ =
      stateAt i p k.castSucc.succ := by
  cases n with
  | zero => exact Fin.elim0 k
  | succ n =>
      refine Fin.cases ?_ ?_ k
      · rfl
      · intro k
        simp [stateAt]

private theorem prefixHistory_endpoint_eq_stateAt [Fintype ι] [DecidableEq ι]
    {n : ℕ} (i : ι)
    (p : Fin (n + 1) → ι) :
    historyOfSuccessors n i (fun k => p k.castSucc)
      ⟨n, Finset.mem_Iic.mpr (Nat.le_refl n)⟩ =
      stateAt i p (Fin.last n).castSucc := by
  cases n with
  | zero => simp [historyOfSuccessors, stateAt]
  | succ n => simp [historyOfSuccessors, stateAt, Fin.last]

variable [Fintype ι] [DecidableEq ι]

/-- Restricting a finite trajectory law to time zero gives its prescribed
initial history, and hence the initial state almost everywhere. -/
theorem finiteTrajectoryKernel_initial_ae
    (P : Matrix ι ι ℝ) (hP : P ∈ Matrix.rowStochastic ℝ ι)
    (n : ℕ) (i : ι) :
    ∀ᵐ x ∂ finiteTrajectoryKernel P hP 0 n (fun _ => i),
      trajectoryInitial n x = i := by
  let μ := finiteTrajectoryKernel P hP 0 n (fun _ => i)
  let r : (Π _ : Finset.Iic n, ι) → (Π _ : Finset.Iic 0, ι) :=
    Preorder.frestrictLe₂ (π := fun _ : ℕ => ι) (Nat.zero_le n)
  let z : (Π _ : Finset.Iic 0, ι) → ι :=
    fun y => y ⟨0, Finset.mem_Iic.mpr (Nat.zero_le 0)⟩
  have hprefix : Measure.map r μ = Measure.dirac (fun _ : Finset.Iic 0 => i) := by
    exact partialTraj_output_prefix_is_dirac P hP 0 n (Nat.zero_le n) (fun _ => i)
  have hz : Measure.map z (Measure.map r μ) = Measure.dirac i := by
    rw [hprefix]
    simp [z]
  have hz' : Measure.map (z ∘ r) μ = Measure.dirac i := by
    rw [← Measure.map_map (by fun_prop) (by fun_prop)]
    exact hz
  have hset : {y : ι | y = i} ∈ ae (Measure.dirac i) := by simp
  have hae : (z ∘ r) ⁻¹' {i} ∈ ae μ :=
    (mem_ae_map_iff (by fun_prop) (MeasurableSet.singleton i)).mp
      (by simp [hz'])
  have hmap : z ∘ r = trajectoryInitial n := by
    funext x
    rfl
  change ∀ᵐ x ∂μ, x ∈ (z ∘ r) ⁻¹' {i} at hae
  simpa [hmap] using hae

/-- The mapped successor-path atom is the unique compatible history atom.
This is the measure-theoretic reduction of the full law to its singleton
mass induction. -/
theorem finiteTrajectorySuccessorLaw_apply_singleton
    (P : Matrix ι ι ℝ) (hP : P ∈ Matrix.rowStochastic ℝ ι)
    (n : ℕ) (i : ι) (p : Fin n → ι) :
    finiteTrajectorySuccessorLaw P hP n i {p} =
      finiteTrajectoryKernel P hP 0 n (fun _ => i)
        {historyOfSuccessors n i p} := by
  let μ := finiteTrajectoryKernel P hP 0 n (fun _ => i)
  have hmeas : Measurable
      (FiniteMarkovTrajectoryFullLawCandidate.trajectorySuccessors (ι := ι) n) := by
    fun_prop
  rw [finiteTrajectorySuccessorLaw]
  change Measure.map
      (FiniteMarkovTrajectoryFullLawCandidate.trajectorySuccessors (ι := ι) n)
      μ {p} = μ {historyOfSuccessors n i p}
  rw [Measure.map_apply (μ := μ) hmeas (MeasurableSet.singleton p)]
  let starts : Set (Π _ : Finset.Iic n, ι) :=
    {x | trajectoryInitial n x = i}
  let fiber : Set (Π _ : Finset.Iic n, ι) :=
    (trajectorySuccessors n) ⁻¹' {p}
  have hrestrict : μ (starts ∩ fiber) = μ fiber := by
    exact Measure.measure_inter_eq_of_ae
      (finiteTrajectoryKernel_initial_ae P hP n i)
  have hfiber :
      starts ∩ fiber = {historyOfSuccessors n i p} := by
    dsimp [starts, fiber]
    simpa only [Set.inter_def, Set.mem_ofPred_eq, Set.mem_preimage,
      Set.mem_singleton_iff, trajectoryInitial] using successorFiber_eq_singleton i p
  rw [← hrestrict, hfiber]

/-- The singleton kernel mass along the canonical history agrees with the
recursive successor-path PMF mass. -/
theorem finiteTrajectoryKernel_history_mass_eq_successorPathPMF
    (P : Matrix ι ι ℝ) (hP : P ∈ Matrix.rowStochastic ℝ ι) :
    ∀ (n : ℕ) (i : ι) (p : Fin n → ι),
      finiteTrajectoryKernel P hP 0 n (fun _ => i)
        {historyOfSuccessors n i p} = successorPathPMF P hP n i p := by
  intro n
  induction n with
  | zero =>
      intro i p
      have hp : p = Fin.elim0 := by funext k; exact Fin.elim0 k
      subst p
      have hx : historyOfSuccessors 0 i Fin.elim0 = (fun _ => i) := by
        funext t
        have ht : t = ⟨0, Finset.mem_Iic.mpr (Nat.zero_le 0)⟩ := Subsingleton.elim _ _
        rw [ht]
        simp [historyOfSuccessors]
      rw [hx]
      change Kernel.id (fun _ : Finset.Iic 0 => i)
        {fun _ : Finset.Iic 0 => i} = _
      rw [Kernel.id_apply]
      simp [successorPathPMF]
  | succ n ih =>
      intro i p
      let x := historyOfSuccessors (n + 1) i p
      have hprefix :
          prefixState n x =
            historyOfSuccessors n i (fun k => p k.castSucc) := by
        funext t
        by_cases ht : t.1 = 0
        · have ht0 : t = ⟨0, Finset.mem_Iic.mpr (Nat.zero_le n)⟩ :=
            Subtype.ext ht
          rw [ht0]
          simp [x, historyOfSuccessors, prefixState]
        · have htpos : 0 < t.1 := Nat.pos_of_ne_zero ht
          have htle : t.1 ≤ n := Finset.mem_Iic.mp t.2
          let k : Fin n := ⟨t.1 - 1, by omega⟩
          have hcoord : t = ⟨k.val + 1, Finset.mem_Iic.mpr (by omega)⟩ := by
            apply Subtype.ext
            change t.1 = k.val + 1
            simp [k]
            omega
          rw [hcoord]
          simp [x, historyOfSuccessors, prefixState, k]
      have hfinal : finalState n x = p (Fin.last n) := by
        simp [x, finalState, historyOfSuccessors, Fin.last]
      have hpenultimate := prefixHistory_endpoint_eq_stateAt i p
      rw [finiteTrajectoryKernel_singleton_recurrence P hP n i
        (historyOfSuccessors (n + 1) i p), hprefix, hfinal]
      rw [ih i (fun k => p k.castSucc)]
      rw [successorPathPMF_apply_eq_prod P hP (n + 1) i p,
        Fin.prod_univ_castSucc]
      rw [successorPathPMF_apply_eq_prod P hP n i (fun k => p k.castSucc)]
      rw [hpenultimate]
      apply congrArg (fun z => z * ENNReal.ofReal
        (P (stateAt i p (Fin.last n).castSucc) (stateAt i p (Fin.last n).succ)))
      apply Finset.prod_congr rfl
      intro k hk
      rw [stateAt_prefix_castSucc]
      rw [stateAt_prefix_succ]

/-- The production finite trajectory kernel, projected to its successor
coordinates, is exactly the recursively defined successor-path PMF. -/
theorem finiteTrajectorySuccessorLaw_eq_successorPathPMF_toMeasure
    (P : Matrix ι ι ℝ) (hP : P ∈ Matrix.rowStochastic ℝ ι)
    (n : ℕ) (i : ι) :
    finiteTrajectorySuccessorLaw P hP n i =
      (successorPathPMF P hP n i).toMeasure := by
  apply Measure.ext_of_singleton
  intro p
  rw [finiteTrajectorySuccessorLaw_apply_singleton P hP n i p,
    finiteTrajectoryKernel_history_mass_eq_successorPathPMF P hP n i p]
  simp

end InfoGeometry.QuantumContext.FiniteMarkovTrajectoryFullSuccessorLaw
end
