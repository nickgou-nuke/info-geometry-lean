/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.QuantumContext.FiniteMarkovHittingPMFExpectation
import InfoGeometry.QuantumContext.FiniteMarkovSuccessorPathMass
import InfoGeometry.QuantumContext.FiniteMarkovTrajectoryCoordinates
import InfoGeometry.QuantumContext.FiniteMarkovTrajectorySingletonRecurrence
import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-!
# Full finite-horizon successor-path law

This owner identifies the successor-coordinate pushforward of the production
`partialTraj` kernel with the recursively generated successor-path PMF.
-/

noncomputable section

namespace InfoGeometry.QuantumContext.FiniteMarkovTrajectorySuccessorLaw

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
open InfoGeometry.QuantumContext.FiniteMarkovTransitionKernel
open InfoGeometry.QuantumContext.FiniteMarkovHittingPMFExpectation
open InfoGeometry.QuantumContext.FiniteMarkovTrajectoryCoordinates
open InfoGeometry.QuantumContext.FiniteMarkovTrajectorySingletonRecurrence
open InfoGeometry.QuantumContext.FiniteMarkovSuccessorPathMass

variable {ι : Type*}

local instance : MeasurableSpace ι := ⊤
local instance : MeasurableSingletonClass ι := inferInstance

variable [Fintype ι] [DecidableEq ι]

/-- Push the production finite-horizon trajectory law to successor
coordinates, omitting its fixed time-zero state. -/
def finiteTrajectorySuccessorLaw (P : Matrix ι ι ℝ)
    (hP : P ∈ Matrix.rowStochastic ℝ ι) (n : ℕ) (i : ι) :
    Measure (Fin n → ι) :=
  (finiteTrajectoryKernel P hP 0 n (fun _ => i)).map (trajectorySuccessors n)

omit [Fintype ι] [DecidableEq ι] in
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

omit [Fintype ι] [DecidableEq ι] in
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

omit [Fintype ι] [DecidableEq ι] in
private theorem prefixHistory_endpoint_eq_stateAt {n : ℕ} (i : ι)
    (p : Fin (n + 1) → ι) :
    historyOfSuccessors n i (fun k => p k.castSucc)
      ⟨n, Finset.mem_Iic.mpr (Nat.le_refl n)⟩ =
      stateAt i p (Fin.last n).castSucc := by
  cases n with
  | zero => simp [historyOfSuccessors, stateAt]
  | succ n => simp [historyOfSuccessors, stateAt, Fin.last]

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
      (trajectorySuccessors (ι := ι) n) := by
    fun_prop
  rw [finiteTrajectorySuccessorLaw]
  change Measure.map
      (trajectorySuccessors (ι := ι) n)
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

/-- The recursive successor-path law's terminal-observable expectation is the
`n`-step matrix action on that observable. The induction follows its
first-transition PMF bind, so the matrix power is composed on the left. -/
theorem successorPathPMF_integral_terminal_eq_pow
    (P : Matrix ι ι ℝ) (hP : P ∈ Matrix.rowStochastic ℝ ι)
    (f : ι → ℝ) :
    ∀ (n : ℕ) (i : ι),
      ∫ path, f (stateAt i path (Fin.last n)) ∂
        (successorPathPMF P hP n i).toMeasure = ((P ^ n).mulVec f) i := by
  intro n
  induction n with
  | zero =>
      intro i
      simp [successorPathPMF, stateAt, Matrix.one_mulVec]
  | succ n ih =>
      intro i
      change (∫ path, f (stateAt i path (Fin.last (n + 1))) ∂
        ((rowPMF P hP i).bind fun j =>
          (successorPathPMF P hP n j).map (fun tail => Fin.cons j tail)).toMeasure) = _
      rw [integral_bind_fintype]
      have hterminal (j : ι) (tail : Fin n → ι) :
          stateAt i (Fin.cons j tail) (Fin.last (n + 1)) =
            stateAt j tail (Fin.last n) := by
        simp [stateAt, Fin.last, Fin.cons]
      have hmap (j : ι) :
          (∫ path, f (stateAt i path (Fin.last (n + 1))) ∂
            ((successorPathPMF P hP n j).map (fun tail => Fin.cons j tail)).toMeasure) =
          ∫ tail, f (stateAt j tail (Fin.last n)) ∂
            (successorPathPMF P hP n j).toMeasure := by
        rw [integral_map_fintype _ _ _ Measurable.of_discrete
          StronglyMeasurable.of_discrete]
        apply integral_congr_ae
        filter_upwards [] with tail
        rw [hterminal]
      simp_rw [hmap, ih]
      calc
        (∑ j, (rowPMF P hP i j).toReal * ((P ^ n).mulVec f) j) =
            (P.mulVec ((P ^ n).mulVec f)) i := by
              simp [Matrix.mulVec, dotProduct, rowPMF,
                ENNReal.toReal_ofReal, Matrix.nonneg_of_mem_rowStochastic hP]
        _ = ((P * P ^ n).mulVec f) i := by
              rw [← Matrix.mulVec_mulVec]
        _ = ((P ^ (n + 1)).mulVec f) i := by
              rw [pow_succ']

/-- The terminal observable of the production trajectory's successor-coordinate
law has expectation given by the corresponding finite matrix power. -/
theorem finiteTrajectorySuccessorLaw_integral_terminal_eq_pow
    (P : Matrix ι ι ℝ) (hP : P ∈ Matrix.rowStochastic ℝ ι)
    (f : ι → ℝ) (n : ℕ) (i : ι) :
    ∫ path, f (stateAt i path (Fin.last n)) ∂
      finiteTrajectorySuccessorLaw P hP n i = ((P ^ n).mulVec f) i := by
  rw [finiteTrajectorySuccessorLaw_eq_successorPathPMF_toMeasure]
  exact successorPathPMF_integral_terminal_eq_pow P hP f n i

/-- A time coordinate in a path whose first `n` steps precede a lag of `m`. -/
def correlationTimeIndex (m n : ℕ) : Fin (m + n + 1) :=
  ⟨n, by omega⟩

/-- Two-observable finite-time correlation for the recursive successor-path
law. Starting at time `n`, the second observation is `m` transitions later.
The future observable is first propagated across the lag, multiplied by the
present observable, then propagated across the initial `n` transitions. -/
theorem successorPathPMF_integral_two_time_product_eq_pow
    (P : Matrix ι ι ℝ) (hP : P ∈ Matrix.rowStochastic ℝ ι)
    (f g : ι → ℝ) (m : ℕ) :
    ∀ (n : ℕ) (i : ι),
      ∫ path,
        f (stateAt i path (correlationTimeIndex m n)) *
          g (stateAt i path (Fin.last (m + n))) ∂
        (successorPathPMF P hP (m + n) i).toMeasure =
      ((P ^ n).mulVec (fun x => f x * ((P ^ m).mulVec g) x)) i := by
  intro n
  induction n with
  | zero =>
      intro i
      have hstart : correlationTimeIndex m 0 = 0 := by
        apply Fin.ext
        rfl
      rw [hstart]
      simp only [Nat.add_zero]
      simp only [stateAt_zero]
      rw [integral_const_mul]
      rw [successorPathPMF_integral_terminal_eq_pow P hP g m i]
      calc
        f i * ((P ^ m).mulVec g) i =
            ((1 : Matrix ι ι ℝ).mulVec
              (fun x => f x * ((P ^ m).mulVec g) x)) i := by
                simp [Matrix.one_mulVec]
        _ = ((P ^ 0).mulVec
              (fun x => f x * ((P ^ m).mulVec g) x)) i := by
                rw [pow_zero]
  | succ n ih =>
      intro i
      change (∫ path,
        f (stateAt i path (correlationTimeIndex m (n + 1))) *
          g (stateAt i path (Fin.last ((m + n) + 1))) ∂
        ((rowPMF P hP i).bind fun j =>
          (successorPathPMF P hP (m + n) j).map
            (fun tail => Fin.cons j tail)).toMeasure) = _
      rw [integral_bind_fintype]
      have htime : correlationTimeIndex m (n + 1) =
          (correlationTimeIndex m n).succ := by
        apply Fin.ext
        rfl
      have hpair (j : ι) (tail : Fin (m + n) → ι) :
          stateAt i (Fin.cons j tail) (correlationTimeIndex m (n + 1)) =
            stateAt j tail (correlationTimeIndex m n) := by
        rw [htime, stateAt_succ]
        simp [stateAt, Fin.cons]
      have hterminal (j : ι) (tail : Fin (m + n) → ι) :
          stateAt i (Fin.cons j tail) (Fin.last ((m + n) + 1)) =
            stateAt j tail (Fin.last (m + n)) := by
        simp [stateAt, Fin.last, Fin.cons]
      have hmap (j : ι) :
          (∫ path,
            f (stateAt i path (correlationTimeIndex m (n + 1))) *
              g (stateAt i path (Fin.last ((m + n) + 1))) ∂
            ((successorPathPMF P hP (m + n) j).map
              (fun tail => Fin.cons j tail)).toMeasure) =
          ∫ tail,
            f (stateAt j tail (correlationTimeIndex m n)) *
              g (stateAt j tail (Fin.last (m + n))) ∂
            (successorPathPMF P hP (m + n) j).toMeasure := by
        rw [integral_map_fintype _ _ _ Measurable.of_discrete
          StronglyMeasurable.of_discrete]
        apply integral_congr_ae
        filter_upwards [] with tail
        rw [hpair, hterminal]
      simp_rw [hmap, ih]
      calc
        (∑ j, (rowPMF P hP i j).toReal *
            ((P ^ n).mulVec
              (fun x => f x * ((P ^ m).mulVec g) x)) j) =
            (P.mulVec ((P ^ n).mulVec
              (fun x => f x * ((P ^ m).mulVec g) x))) i := by
                simp [Matrix.mulVec, dotProduct, rowPMF,
                  ENNReal.toReal_ofReal,
                  Matrix.nonneg_of_mem_rowStochastic hP]
        _ = ((P * P ^ n).mulVec
              (fun x => f x * ((P ^ m).mulVec g) x)) i := by
                rw [← Matrix.mulVec_mulVec]
        _ = ((P ^ (n + 1)).mulVec
              (fun x => f x * ((P ^ m).mulVec g) x)) i := by
                rw [pow_succ']

/-- The production trajectory law has the same arbitrary finite-time
two-observable correlation as the recursive successor-path law. -/
theorem finiteTrajectorySuccessorLaw_integral_two_time_product_eq_pow
    (P : Matrix ι ι ℝ) (hP : P ∈ Matrix.rowStochastic ℝ ι)
    (f g : ι → ℝ) (m n : ℕ) (i : ι) :
      ∫ path,
        f (stateAt i path (correlationTimeIndex m n)) *
          g (stateAt i path (Fin.last (m + n))) ∂
        finiteTrajectorySuccessorLaw P hP (m + n) i =
      ((P ^ n).mulVec (fun x => f x * ((P ^ m).mulVec g) x)) i := by
  rw [finiteTrajectorySuccessorLaw_eq_successorPathPMF_toMeasure]
  exact successorPathPMF_integral_two_time_product_eq_pow P hP f g m n i

/-- Projecting a production successor-coordinate law at horizon `n + 1` to
its first `n` successor coordinates gives the production law at horizon `n`.
This is finite-horizon marginal consistency, obtained from the prefix map on
Mathlib's `partialTraj` kernel. -/
theorem finiteTrajectorySuccessorLaw_prefix
    (P : Matrix ι ι ℝ) (hP : P ∈ Matrix.rowStochastic ℝ ι)
    (n : ℕ) (i : ι) :
    Measure.map (fun p : Fin (n + 1) → ι => fun k : Fin n => p k.castSucc)
      (finiteTrajectorySuccessorLaw P hP (n + 1) i) =
    finiteTrajectorySuccessorLaw P hP n i := by
  let prefixPath : (Fin (n + 1) → ι) → (Fin n → ι) :=
    fun p k => p k.castSucc
  let prefixHistory : (Π _ : Finset.Iic (n + 1), ι) →
      (Π _ : Finset.Iic n, ι) :=
    Preorder.frestrictLe₂ (π := fun _ : ℕ => ι) (Nat.le_succ n)
  have hcoords :
      prefixPath ∘ trajectorySuccessors (n + 1) =
        trajectorySuccessors n ∘ prefixHistory := by
    funext x
    funext k
    rfl
  change Measure.map prefixPath
      (Measure.map (trajectorySuccessors (n + 1))
        (finiteTrajectoryKernel P hP 0 (n + 1) (fun _ => i))) =
      Measure.map (trajectorySuccessors n)
        (finiteTrajectoryKernel P hP 0 n (fun _ => i))
  rw [Measure.map_map (by fun_prop) (by fun_prop), hcoords,
    ← Measure.map_map (by fun_prop) (by fun_prop)]
  change Measure.map (trajectorySuccessors n)
      (Measure.map prefixHistory
        (Kernel.partialTraj (X := fun _ : ℕ => ι)
          (historyTransitionKernel P hP) 0 (n + 1)
          (fun _ => i))) = _
  rw [Kernel.partialTraj_map_frestrictLe₂_apply
    (X := fun _ : ℕ => ι) (κ := historyTransitionKernel P hP)
    (a := 0) (b := n) (c := n + 1)
    (fun _ => i) (Nat.le_succ n)]
  rfl

end InfoGeometry.QuantumContext.FiniteMarkovTrajectorySuccessorLaw
end
