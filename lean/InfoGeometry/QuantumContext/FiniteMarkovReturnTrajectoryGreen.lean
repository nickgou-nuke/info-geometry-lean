/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.QuantumContext.FiniteMarkovTrajectoryHittingGreen
import InfoGeometry.QuantumContext.MarkovAttentionKemenyTrace

/-!
# Finite first-return trajectory Green identity

The return cost counts at least one transition. Its finite-horizon integrals
are formed from the production successor-coordinate trajectory law. The
theorem identifies their order supremum with the return-adjusted group-inverse
potential; it does not define an expectation on infinite paths.
-/

noncomputable section

namespace InfoGeometry.QuantumContext.FiniteMarkovReturnTrajectoryGreen

open MeasureTheory ProbabilityTheory
open InfoGeometry.Canonical.HartwigSouriauFrameDrazin
open InfoGeometry.QuantumContext.FiniteMarkovTrajectoryHittingGreen
open InfoGeometry.QuantumContext.FiniteMarkovHittingPMFExpectation
open InfoGeometry.QuantumContext.FiniteMarkovTrajectorySuccessorLaw
open InfoGeometry.QuantumContext.FiniteMarkovHittingColimitGreen
open InfoGeometry.QuantumContext.FiniteMarkovDirichletApproximation
open InfoGeometry.QuantumContext.FiniteMarkovDirichletOrderColimit
open InfoGeometry.QuantumContext.MarkovDrazin
open InfoGeometry.QuantumContext.FiniteMarkovTransitionKernel
open scoped BigOperators ENNReal

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

local instance : MeasurableSpace ι := ⊤
local instance : MeasurableSingletonClass ι := inferInstance
local instance (n : ℕ) : MeasurableSpace (Fin n → ι) := MeasurableSpace.pi
local instance (n : ℕ) : MeasurableSingletonClass (Fin n → ι) := inferInstance

/-- First passage counted after the first successor step. At positive
horizon this is one plus the first-hit cost of the tail path, including when
the initial state already equals the target. -/
def pathFirstPassageAfterStepCost (target : ι) :
    (n : ℕ) → ι → (Fin n → ι) → ℝ
  | 0, _, _ => 0
  | n + 1, _, path =>
      1 + pathFirstHitCost target n (path 0) (fun k => path k.succ)

/-- When the initial state differs from the target, counting after the first
successor gives exactly the existing truncated first-hit path cost. -/
theorem pathFirstPassageAfterStepCost_eq_pathFirstHitCost_of_ne
    (target start : ι) (hstart : start ≠ target) :
    ∀ (n : ℕ) (path : Fin n → ι),
      pathFirstPassageAfterStepCost target n start path =
        pathFirstHitCost target n start path := by
  intro n
  cases n with
  | zero => intro path; simp [pathFirstPassageAfterStepCost, pathFirstHitCost]
  | succ n => intro path; simp [pathFirstPassageAfterStepCost, pathFirstHitCost, hstart]

private def prependReturnPath {n : ℕ} (state : ι) (tail : Fin n → ι) :
    Fin (n + 1) → ι := @Fin.cons n (fun _ => ι) state tail

private theorem prependReturnCost_integral (P : Matrix ι ι ℝ)
    (hP : P ∈ Matrix.rowStochastic ℝ ι) (target j : ι) (n : ℕ) :
    ∫ path, pathFirstPassageAfterStepCost target (n + 1) j path
      ∂(PMF.map (prependReturnPath j) (successorPathPMF P hP n j)).toMeasure =
      1 + successorPathExpectedCost P hP target n j := by
  rw [integral_map_fintype _ _ _ Measurable.of_discrete StronglyMeasurable.of_discrete]
  rw [show (fun path : Fin n → ι =>
      pathFirstPassageAfterStepCost target (n + 1) j (prependReturnPath j path)) =
      fun path => 1 + pathFirstHitCost target n j path from by
        funext path
        simp [pathFirstPassageAfterStepCost, pathFirstHitCost, prependReturnPath,
          Fin.cons]]
  rw [PMF.integral_eq_sum]
  simp only [smul_eq_mul]
  have hmass :
      ∑ path, (successorPathPMF P hP n j path).toReal = 1 := by
    simpa using (PMF.integral_eq_sum (successorPathPMF P hP n j)
      (fun _ => (1 : ℝ))).symm
  calc
    (∑ path, (successorPathPMF P hP n j path).toReal *
        (1 + pathFirstHitCost target n j path)) =
      (∑ path, (successorPathPMF P hP n j path).toReal) +
        successorPathExpectedCost P hP target n j := by
          simp_rw [mul_add]
          rw [Finset.sum_add_distrib]
          simp [successorPathExpectedCost, PMF.integral_eq_sum, smul_eq_mul]
    _ = 1 + successorPathExpectedCost P hP target n j := by rw [hmass]

private theorem rowPMF_integral_eq_sum (P : Matrix ι ι ℝ)
    (hP : P ∈ Matrix.rowStochastic ℝ ι) (i : ι) (x : ι → ℝ) :
    ∫ j, x j ∂(rowPMF P hP i).toMeasure =
      ∑ j, (rowPMF P hP i j).toReal * x j := by
  rw [PMF.integral_eq_sum]
  simp only [smul_eq_mul]

private theorem rowPMF_integral_eq_mulVec (P : Matrix ι ι ℝ)
    (hP : P ∈ Matrix.rowStochastic ℝ ι) (i : ι) (x : ι → ℝ) :
    ∫ j, x j ∂(rowPMF P hP i).toMeasure = (P.mulVec x) i := by
  rw [PMF.integral_eq_sum]
  simp [rowPMF, Matrix.mulVec, dotProduct,
    Matrix.nonneg_of_mem_rowStochastic hP]

private theorem sum_erase_eq_sub_target (f : ι → ℝ) (target : ι)
    (s : ℝ) (hsum : ∑ i, f i = s) :
    (∑ i ∈ Finset.univ.erase target, f i) = s - f target := by
  have hsplit := Finset.sum_erase_add (Finset.univ : Finset ι)
    f (Finset.mem_univ target)
  rw [hsum] at hsplit
  linarith

private theorem weighted_sum_target_eq (π f : ι → ℝ) (target : ι)
    (hzero : ∑ i, π i * f i = 0)
    (herase : ∑ i ∈ Finset.univ.erase target, π i * f i = 1 - π target) :
    π target * f target = π target - 1 := by
  have hsplit := Finset.sum_erase_add (Finset.univ : Finset ι)
    (fun i => π i * f i) (Finset.mem_univ target)
  rw [hzero, herase] at hsplit
  linarith

private theorem weighted_target_solve (p y : ℝ) (hp : p ≠ 0)
    (hprod : p * y = p - 1) : y = 1 - p⁻¹ := by
  calc
    y = p⁻¹ * (p * y) := by rw [← mul_assoc, inv_mul_cancel₀ hp, one_mul]
    _ = p⁻¹ * (p - 1) := by rw [hprod]
    _ = 1 - p⁻¹ := by rw [mul_sub, inv_mul_cancel₀ hp, mul_one]

private theorem sum_eq_target_add_erase (f : ι → ℝ) (target : ι) :
    (∑ i, f i) = f target + ∑ i ∈ Finset.univ.erase target, f i := by
  have hsplit := Finset.sum_erase_add (Finset.univ : Finset ι)
    f (Finset.mem_univ target)
  simpa [add_comm] using hsplit.symm

/-- At positive horizon, the after-step cost integral is one plus the
transition average of the existing finite first-hit approximation. -/
theorem trajectoryLaw_integral_afterStepCost_succ_eq_one_add_mulVec
    (P : Matrix ι ι ℝ) (hP : P ∈ Matrix.rowStochastic ℝ ι)
    (target i : ι) (n : ℕ) :
    (∫ path, pathFirstPassageAfterStepCost target (n + 1) i path ∂
      finiteTrajectorySuccessorLaw P hP (n + 1) i) =
      1 + (P.mulVec (firstHitApproximation P target n)) i := by
  rw [finiteTrajectorySuccessorLaw_eq_successorPathPMF_toMeasure]
  rw [show successorPathPMF P hP (n + 1) i =
    (rowPMF P hP i).bind fun j =>
      (successorPathPMF P hP n j).map (prependReturnPath j) from rfl,
    integral_bind_fintype]
  have hmass : ∑ j, (rowPMF P hP i j).toReal = 1 := by
    simpa using (PMF.integral_eq_sum (rowPMF P hP i) (fun _ => (1 : ℝ))).symm
  have hrecurrence :
      (∑ j, (rowPMF P hP i j).toReal *
        ∫ path, pathFirstPassageAfterStepCost target (n + 1) i path
          ∂(PMF.map (prependReturnPath j) (successorPathPMF P hP n j)).toMeasure) =
      1 + ∫ j, successorPathExpectedCost P hP target n j
        ∂(rowPMF P hP i).toMeasure := by
    calc
      (∑ j, (rowPMF P hP i j).toReal *
          ∫ path, pathFirstPassageAfterStepCost target (n + 1) i path
            ∂(PMF.map (prependReturnPath j) (successorPathPMF P hP n j)).toMeasure) =
        ∑ j, (rowPMF P hP i j).toReal *
          (1 + successorPathExpectedCost P hP target n j) := by
            apply Finset.sum_congr rfl
            intro j hj
            exact congrArg _ (prependReturnCost_integral P hP target j n)
      _ = 1 + ∑ j, (rowPMF P hP i j).toReal *
          successorPathExpectedCost P hP target n j := by
            simp_rw [mul_add]
            rw [Finset.sum_add_distrib]
            simp only [mul_one]
            rw [hmass]
      _ = 1 + ∫ j, successorPathExpectedCost P hP target n j
          ∂(rowPMF P hP i).toMeasure := by
            rw [rowPMF_integral_eq_sum]
  rw [hrecurrence]
  have hcost :
      (fun j => successorPathExpectedCost P hP target n j) =
        firstHitApproximation P target n := by
    funext j
    exact successorPathExpectedCost_eq_firstHitApproximation P hP target n j
  rw [hcost, rowPMF_integral_eq_mulVec P hP i]

/-- For positive finite row-stochastic transitions, the group-inverse
potential has the target-coordinate identity needed by the return recurrence.
It follows from stationarity and its off-target Laplacian equation. -/
theorem groupInversePotentialDifference_target_mulVec_eq_inv_sub_one
    (P G : Matrix ι ι ℝ) (π : ι → ℝ)
    (hP : P ∈ Matrix.rowStochastic ℝ ι)
    (hPpos : ∀ i j, 0 < P i j)
    (hπnonneg : ∀ i, 0 ≤ π i)
    (hπsum : ∑ i, π i = 1)
    (hπstat : ∀ j, ∑ i, π i * P i j = π j)
    (hG : IsGroupInverse (1 - P) G) (target : ι) :
    (P.mulVec (fun j => groupInversePotentialDifference π G j target)) target =
      (π target)⁻¹ - 1 := by
  have hπpos := stationaryRowProbability_pos_of_pos_entries
    P π hPpos hπnonneg hπsum hπstat target
  have hoff := groupInversePotentialDifference_laplacian_eq_one_off_target
    P G π hP hPpos hπnonneg hπsum hπstat hG target
  let h : ι → ℝ := fun i => groupInversePotentialDifference π G i target
  have hboundary : h target = 0 := by
    simp [h, groupInversePotentialDifference]
  have hLap : ∑ i, π i * ((1 - P).mulVec h) i = 0 :=
    weightedMeanMap_laplacian_eq_zero P π h hπstat
  have hsumRest :
      ∑ i ∈ Finset.univ.erase target, π i * ((1 - P).mulVec h) i =
        1 - π target := by
    calc
      (∑ i ∈ Finset.univ.erase target, π i * ((1 - P).mulVec h) i) =
          ∑ i ∈ Finset.univ.erase target, π i := by
            apply Finset.sum_congr rfl
            intro i hi
            rw [hoff i (Finset.ne_of_mem_erase hi), mul_one]
      _ = 1 - π target := sum_erase_eq_sub_target π target 1 hπsum
  have hsum :
      (∑ i, π i * ((1 - P).mulVec h) i) =
        π target * ((1 - P).mulVec h) target + (1 - π target) := by
    rw [sum_eq_target_add_erase, hsumRest]
  have hπne : π target ≠ 0 := hπpos.ne'
  have hLtarget : ((1 - P).mulVec h) target = 1 - (π target)⁻¹ := by
    have hprod : π target * ((1 - P).mulVec h) target = π target - 1 := by
      exact weighted_sum_target_eq π (fun i => ((1 - P).mulVec h) i)
        target hLap hsumRest
    exact weighted_target_solve (π target) ((1 - P).mulVec h target) hπne hprod
  have hLformula : ((1 - P).mulVec h) target =
      h target - (P.mulVec h) target := by
    simp [Matrix.sub_mulVec, Matrix.one_mulVec]
  rw [hboundary] at hLformula
  rw [hLformula] at hLtarget
  linear_combination -hLtarget

/-- The order supremum of the finite first-passage-after-step trajectory
integrals is the return-adjusted group-inverse potential. This includes the
diagonal first-return case. -/
theorem trajectoryLaw_afterStepCost_sup_eq_groupInverseReturnAdjustedPotential
    (P G : Matrix ι ι ℝ) (π : ι → ℝ)
    (hP : P ∈ Matrix.rowStochastic ℝ ι)
    (hPpos : ∀ i j, 0 < P i j)
    (hπnonneg : ∀ i, 0 ≤ π i)
    (hπsum : ∑ i, π i = 1)
    (hπstat : ∀ j, ∑ i, π i * P i j = π j)
    (hG : IsGroupInverse (1 - P) G) (target start : ι) :
    sSup (Set.range (fun horizon =>
      ∫ path, pathFirstPassageAfterStepCost target horizon start path ∂
        finiteTrajectorySuccessorLaw P hP horizon start)) =
      groupInverseReturnAdjustedPotential π G start target := by
  by_cases hstart : start = target
  · subst start
    obtain ⟨ε, hε, hminor⟩ := exists_target_minorization_of_positive P target hPpos
    let costs : ℕ → ι → ℝ := fun n j => firstHitApproximation P target n j
    let weighted : ℕ → ℝ := fun n =>
      ∑ j ∈ Finset.univ, P target j * costs n j
    have hmono (j : ι) : Monotone (fun n => costs n j) := by
      apply monotone_nat_of_le_succ
      intro n
      exact firstHitApproximation_mono P hP target n j
    have hcostBound (n : ℕ) (j : ι) : costs n j ≤ ε⁻¹ := by
      exact firstHitApproximation_le_inv_of_target_minorization
        P hP target ε hε hminor n j
    have hcostBdd (j : ι) : BddAbove (Set.range (fun n => costs n j)) := by
      refine ⟨ε⁻¹, ?_⟩
      rintro y ⟨n, rfl⟩
      exact hcostBound n j
    have hweightedSup := csSup_range_weighted_finset_sum_of_monotone
      Finset.univ (fun j => P target j) costs
      (fun j => Matrix.nonneg_of_mem_rowStochastic hP)
      hmono (fun _ => ε⁻¹) hcostBound
    have hweightedPotential :
        sSup (Set.range weighted) =
          (P.mulVec (fun j => groupInversePotentialDifference π G j target)) target := by
      change sSup (Set.range (fun n =>
        ∑ j ∈ Finset.univ, P target j * firstHitApproximation P target n j)) = _
      rw [hweightedSup]
      calc
        (∑ j ∈ Finset.univ,
            sSup (Set.range (fun n => P target j * firstHitApproximation P target n j))) =
            ∑ j ∈ Finset.univ,
              P target j * firstHitApproximationColimit P hP target j := by
                apply Finset.sum_congr rfl
                intro j hj
                calc
                  sSup (Set.range (fun n => P target j *
                    firstHitApproximation P target n j)) =
                      P target j * sSup (Set.range
                        (fun n => firstHitApproximation P target n j)) :=
                    csSup_range_mul_left_of_nonneg (P target j)
                      (Matrix.nonneg_of_mem_rowStochastic hP)
                      (fun n => firstHitApproximation P target n j) (hcostBdd j)
                  _ = P target j * firstHitApproximationColimit P hP target j := by
                    unfold firstHitApproximationColimit
                    change P target j * sSup (Set.range
                      (fun n => firstHitApproximation P target n j)) =
                      P target j * sSup (Set.range
                        (fun n => firstHitApproximation P target n j))
                    rfl
        _ = ∑ j ∈ Finset.univ,
              P target j * groupInversePotentialDifference π G j target := by
                apply Finset.sum_congr rfl
                intro j hj
                rw [firstHitApproximationColimit_eq_groupInversePotentialDifference
                  P G π hP hPpos hπnonneg hπsum hπstat hG target j]
        _ = (P.mulVec
              (fun j => groupInversePotentialDifference π G j target)) target := by
                simp [Matrix.mulVec, dotProduct]
    have hweightedMono : Monotone weighted := by
      intro n m hnm
      apply Finset.sum_le_sum
      intro j hj
      exact mul_le_mul_of_nonneg_left (hmono j hnm)
        (Matrix.nonneg_of_mem_rowStochastic hP)
    have hweightedBdd : BddAbove (Set.range weighted) := by
      refine ⟨∑ j, P target j * ε⁻¹, ?_⟩
      rintro z ⟨n, rfl⟩
      dsimp [weighted]
      exact Finset.sum_le_sum fun j hj =>
        mul_le_mul_of_nonneg_left (hcostBound n j)
          (Matrix.nonneg_of_mem_rowStochastic hP)
    have htailSup : sSup (Set.range (fun n => 1 + weighted n)) =
        1 + sSup (Set.range weighted) := by
      simpa using csSup_range_add_of_monotone (fun _ => (1 : ℝ)) weighted
        (monotone_const) hweightedMono
        (⟨1, by rintro y ⟨n, rfl⟩; rfl⟩) hweightedBdd
    let ret : ℕ → ℝ := fun horizon =>
      ∫ path, pathFirstPassageAfterStepCost target horizon target path ∂
        finiteTrajectorySuccessorLaw P hP horizon target
    have hret0 : ret 0 = 0 := by simp [ret, pathFirstPassageAfterStepCost]
    have hretSucc (n : ℕ) : ret (n + 1) = 1 + weighted n := by
      rw [show ret (n + 1) =
        (∫ path, pathFirstPassageAfterStepCost target (n + 1) target path ∂
          finiteTrajectorySuccessorLaw P hP (n + 1) target) from rfl,
        trajectoryLaw_integral_afterStepCost_succ_eq_one_add_mulVec]
      simp only [weighted, costs]
      rfl
    have hretMono : Monotone ret := by
      apply monotone_nat_of_le_succ
      intro n
      cases n with
      | zero => rw [hret0, hretSucc]; simp [weighted, costs, firstHitApproximation]
      | succ n =>
          rw [hretSucc, hretSucc]
          linarith [hweightedMono (Nat.le_succ n)]
    have hretBdd : BddAbove (Set.range ret) := by
      refine ⟨max 0 (1 + sSup (Set.range weighted)), ?_⟩
      rintro z ⟨n, rfl⟩
      cases n with
      | zero => rw [hret0]; exact le_max_left _ _
      | succ n =>
          rw [hretSucc]
          apply le_trans _ (le_max_right _ _)
          linarith [le_csSup hweightedBdd (Set.mem_range_self n)]
    have hretSup : sSup (Set.range ret) = sSup (Set.range (fun n => ret (n + 1))) :=
      (csSup_range_succ_eq_of_monotone ret hretMono hretBdd).symm
    rw [show (fun horizon =>
      ∫ path, pathFirstPassageAfterStepCost target horizon target path ∂
        finiteTrajectorySuccessorLaw P hP horizon target) = ret from rfl,
      hretSup, show (fun n => ret (n + 1)) = fun n => 1 + weighted n from funext hretSucc,
      htailSup, hweightedPotential,
      groupInversePotentialDifference_target_mulVec_eq_inv_sub_one
        P G π hP hPpos hπnonneg hπsum hπstat hG target]
    simp [groupInverseReturnAdjustedPotential, groupInversePotentialDifference]
  · have hstage (horizon : ℕ) :
      (∫ path, pathFirstPassageAfterStepCost target horizon start path ∂
        finiteTrajectorySuccessorLaw P hP horizon start) =
      ∫ path, pathFirstHitCost target horizon start path ∂
        finiteTrajectorySuccessorLaw P hP horizon start := by
      apply integral_congr_ae
      filter_upwards [] with path
      exact pathFirstPassageAfterStepCost_eq_pathFirstHitCost_of_ne
        target start hstart horizon path
    rw [show (fun horizon =>
      ∫ path, pathFirstPassageAfterStepCost target horizon start path ∂
        finiteTrajectorySuccessorLaw P hP horizon start) =
      fun horizon =>
        ∫ path, pathFirstHitCost target horizon start path ∂
          finiteTrajectorySuccessorLaw P hP horizon start from funext hstage]
    rw [trajectoryLaw_hittingCost_sup_eq_groupInversePotentialDifference
      P G π hP hPpos hπnonneg hπsum hπstat hG target start]
    simp [groupInverseReturnAdjustedPotential, hstart]

end InfoGeometry.QuantumContext.FiniteMarkovReturnTrajectoryGreen

end noncomputable section
