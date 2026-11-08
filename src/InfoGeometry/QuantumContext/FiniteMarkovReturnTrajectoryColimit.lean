/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.CategoryTheory.Functor.OfSequence
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import InfoGeometry.Categorical.InductivePosetColimit
import InfoGeometry.QuantumContext.FiniteMarkovReturnTrajectoryGreen

/-!
# Order colimit of finite Markov return-cost integrals

The objects of this diagram are the production trajectory-law integrals of
the finite-horizon after-step cost. Its colimit is an order colimit in `ℝ`;
the result does not assert an infinite-path expectation.
-/

noncomputable section

namespace InfoGeometry.QuantumContext.FiniteMarkovReturnTrajectoryColimit

open CategoryTheory CategoryTheory.Limits
open MeasureTheory
open InfoGeometry.Categorical.InductivePosetColimit
open InfoGeometry.Canonical.HartwigSouriauFrameDrazin
open InfoGeometry.QuantumContext.FiniteMarkovReturnTrajectoryGreen
open InfoGeometry.QuantumContext.FiniteMarkovTrajectoryHittingGreen
open InfoGeometry.QuantumContext.FiniteMarkovTrajectorySuccessorLaw
open InfoGeometry.QuantumContext.FiniteMarkovHittingPMFExpectation
open InfoGeometry.QuantumContext.FiniteMarkovDirichletApproximation
open InfoGeometry.QuantumContext.FiniteMarkovDirichletOrderColimit
open InfoGeometry.QuantumContext.FiniteMarkovHittingColimitGreen
open InfoGeometry.QuantumContext.MarkovDrazin

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

local instance : MeasurableSpace ι := ⊤
local instance : MeasurableSingletonClass ι := inferInstance
local instance (n : ℕ) : MeasurableSpace (Fin n → ι) := MeasurableSpace.pi
local instance (n : ℕ) : MeasurableSingletonClass (Fin n → ι) := inferInstance

/-- The production-law integral of the finite-horizon after-step cost. -/
def trajectoryLawAfterStepCost
    (P : Matrix ι ι ℝ) (hP : P ∈ Matrix.rowStochastic ℝ ι)
    (target start : ι) (n : ℕ) : ℝ :=
  ∫ path, pathFirstPassageAfterStepCost target n start path ∂
    finiteTrajectorySuccessorLaw P hP n start

/-- Adjacent finite horizons are monotone. Off the diagonal this is the
existing hitting-cost monotonicity; on the diagonal it follows from the
after-step recurrence and nonnegative stochastic row weights. -/
theorem trajectoryLawAfterStepCost_mono
    (P : Matrix ι ι ℝ) (hP : P ∈ Matrix.rowStochastic ℝ ι)
    (target start : ι) (n : ℕ) :
    trajectoryLawAfterStepCost P hP target start n ≤
      trajectoryLawAfterStepCost P hP target start (n + 1) := by
  by_cases hstart : start = target
  · subst start
    cases n with
    | zero =>
        have hzero : trajectoryLawAfterStepCost P hP target target 0 = 0 := by
          simp [trajectoryLawAfterStepCost, pathFirstPassageAfterStepCost]
        have hone : trajectoryLawAfterStepCost P hP target target 1 = 1 := by
          unfold trajectoryLawAfterStepCost
          rw [trajectoryLaw_integral_afterStepCost_succ_eq_one_add_mulVec]
          simp [firstHitApproximation, Matrix.mulVec]
        rw [hzero, hone]
        norm_num
    | succ n =>
        have hleft : trajectoryLawAfterStepCost P hP target target (n + 1) =
            1 + (P.mulVec (firstHitApproximation P target n)) target := by
          exact trajectoryLaw_integral_afterStepCost_succ_eq_one_add_mulVec
            P hP target target n
        have hright : trajectoryLawAfterStepCost P hP target target (n + 1 + 1) =
            1 + (P.mulVec (firstHitApproximation P target (n + 1))) target := by
          simpa [trajectoryLawAfterStepCost, Nat.add_assoc] using
            trajectoryLaw_integral_afterStepCost_succ_eq_one_add_mulVec
              P hP target target (n + 1)
        rw [hleft, hright]
        apply add_le_add_right
        rw [Matrix.mulVec, dotProduct, Matrix.mulVec, dotProduct]
        apply Finset.sum_le_sum
        intro j hj
        exact mul_le_mul_of_nonneg_left
          (firstHitApproximation_mono P hP target n j)
          (Matrix.nonneg_of_mem_rowStochastic hP)
  · have hcost (m : ℕ) :
        trajectoryLawAfterStepCost P hP target start m =
          ∫ path, pathFirstHitCost target m start path ∂
            finiteTrajectorySuccessorLaw P hP m start := by
      unfold trajectoryLawAfterStepCost
      apply MeasureTheory.integral_congr_ae
      filter_upwards [] with path
      exact pathFirstPassageAfterStepCost_eq_pathFirstHitCost_of_ne
        target start hstart m path
    rw [hcost n, hcost (n + 1)]
    exact trajectoryLaw_hittingCost_mono P hP target start n

/-- Monotonicity between arbitrary horizons. -/
theorem trajectoryLawAfterStepCost_mono_of_le
    (P : Matrix ι ι ℝ) (hP : P ∈ Matrix.rowStochastic ℝ ι)
    (target start : ι) {n m : ℕ} (hnm : n ≤ m) :
    trajectoryLawAfterStepCost P hP target start n ≤
      trajectoryLawAfterStepCost P hP target start m := by
  induction m, hnm using Nat.le_induction with
  | base => exact le_rfl
  | succ m hnm ih =>
      exact le_trans ih (trajectoryLawAfterStepCost_mono P hP target start m)

/-- The finite-horizon production return costs form a diagram in the real
preorder category. -/
def trajectoryLawAfterStepCostDiagram
    (P : Matrix ι ι ℝ) (hP : P ∈ Matrix.rowStochastic ℝ ι)
    (target start : ι) : ℕ ⥤ ℝ :=
  Functor.ofSequence (fun n =>
    homOfLE (trajectoryLawAfterStepCost_mono P hP target start n))

/-- The object-range of the return diagram is exactly the range of its
production-law finite-horizon integrals. -/
theorem trajectoryLawAfterStepCostDiagram_range_eq
    (P : Matrix ι ι ℝ) (hP : P ∈ Matrix.rowStochastic ℝ ι)
    (target start : ι) :
    Set.range (trajectoryLawAfterStepCostDiagram P hP target start).obj =
      Set.range (fun n =>
        ∫ path, pathFirstPassageAfterStepCost target n start path ∂
          finiteTrajectorySuccessorLaw P hP n start) := by
  change Set.range (fun n => trajectoryLawAfterStepCost P hP target start n) = _
  rfl

/-- Strict positivity bounds every finite-horizon after-step return integral.
For the diagonal, use its recurrence as one plus a stochastic average of
bounded first-hit approximants. -/
theorem trajectoryLawAfterStepCost_bddAbove
    (P : Matrix ι ι ℝ) (hP : P ∈ Matrix.rowStochastic ℝ ι)
    (hPpos : ∀ i j, 0 < P i j) (target start : ι) :
    BddAbove (Set.range (trajectoryLawAfterStepCost P hP target start)) := by
  obtain ⟨ε, hε, hminor⟩ := exists_target_minorization_of_positive P target hPpos
  by_cases hstart : start = target
  · subst start
    refine ⟨max 0 (1 + ε⁻¹), ?_⟩
    rintro y ⟨n, rfl⟩
    cases n with
    | zero =>
        simp [trajectoryLawAfterStepCost, pathFirstPassageAfterStepCost]
    | succ n =>
        rw [trajectoryLawAfterStepCost,
          trajectoryLaw_integral_afterStepCost_succ_eq_one_add_mulVec]
        have hbound (j : ι) : firstHitApproximation P target n j ≤ ε⁻¹ :=
          firstHitApproximation_le_inv_of_target_minorization
            P hP target ε hε hminor n j
        have hmul :
            (P.mulVec (firstHitApproximation P target n)) target ≤ ε⁻¹ := by
          rw [Matrix.mulVec, dotProduct]
          calc
            (∑ j, P target j * firstHitApproximation P target n j) ≤
                ∑ j, P target j * ε⁻¹ := by
                  apply Finset.sum_le_sum
                  intro j hj
                  exact mul_le_mul_of_nonneg_left (hbound j)
                    (Matrix.nonneg_of_mem_rowStochastic hP)
            _ = ε⁻¹ := by
                  rw [← Finset.sum_mul]
                  rw [Matrix.sum_row_of_mem_rowStochastic hP target]
                  simp
        have hret :
            1 + (P.mulVec (firstHitApproximation P target n)) target ≤
              1 + ε⁻¹ := add_le_add_right hmul 1
        exact le_trans hret (le_max_right _ _)
  · refine ⟨ε⁻¹, ?_⟩
    rintro y ⟨n, rfl⟩
    have hstage : trajectoryLawAfterStepCost P hP target start n =
        firstHitApproximation P target n start := by
      unfold trajectoryLawAfterStepCost
      calc
        (∫ path, pathFirstPassageAfterStepCost target n start path ∂
            finiteTrajectorySuccessorLaw P hP n start) =
          ∫ path, pathFirstHitCost target n start path ∂
            finiteTrajectorySuccessorLaw P hP n start := by
              apply MeasureTheory.integral_congr_ae
              filter_upwards [] with path
              exact pathFirstPassageAfterStepCost_eq_pathFirstHitCost_of_ne
                target start hstart n path
        _ = firstHitApproximation P target n start :=
          trajectoryLaw_integral_pathFirstHitCost_eq_firstHitApproximation
            P hP target start n
    rw [hstage]
    exact firstHitApproximation_le_inv_of_target_minorization
      P hP target ε hε hminor n start

/-- The order-colimit value of finite-horizon after-step costs. -/
noncomputable def trajectoryLawAfterStepCostColimit
    (P : Matrix ι ι ℝ) (hP : P ∈ Matrix.rowStochastic ℝ ι)
    (target start : ι) : ℝ :=
  sSup (Set.range (trajectoryLawAfterStepCostDiagram P hP target start).obj)

/-- Under strict positivity, the production-law return diagram has a least
upper bound. -/
theorem trajectoryLawAfterStepCostColimit_isLUB
    (P : Matrix ι ι ℝ) (hP : P ∈ Matrix.rowStochastic ℝ ι)
    (hPpos : ∀ i j, 0 < P i j) (target start : ι) :
    IsLUB (Set.range (trajectoryLawAfterStepCostDiagram P hP target start).obj)
      (trajectoryLawAfterStepCostColimit P hP target start) := by
  rw [trajectoryLawAfterStepCostDiagram_range_eq]
  change IsLUB (Set.range (trajectoryLawAfterStepCost P hP target start)) _
  exact isLUB_csSup (Set.range_nonempty _)
    (trajectoryLawAfterStepCost_bddAbove P hP hPpos target start)

/-- The finite-horizon return-cost diagram has its canonical preorder
colimit, obtained from the least-upper-bound owner. -/
noncomputable def trajectoryLawAfterStepCostColimitCocone
    (P : Matrix ι ι ℝ) (hP : P ∈ Matrix.rowStochastic ℝ ι)
    (hPpos : ∀ i j, 0 < P i j) (target start : ι) :
    ColimitCocone (trajectoryLawAfterStepCostDiagram P hP target start) :=
  colimitCoconeOfIsLUB
    (trajectoryLawAfterStepCostDiagram P hP target start)
    (trajectoryLawAfterStepCostColimit_isLUB P hP hPpos target start)

/-- The finite-horizon return colimit is the existing group-inverse
return-adjusted potential. -/
theorem trajectoryLawAfterStepCostColimit_eq_groupInverseReturnAdjustedPotential
    (P G : Matrix ι ι ℝ) (π : ι → ℝ)
    (hP : P ∈ Matrix.rowStochastic ℝ ι)
    (hPpos : ∀ i j, 0 < P i j)
    (hπnonneg : ∀ i, 0 ≤ π i)
    (hπsum : ∑ i, π i = 1)
    (hπstat : ∀ j, ∑ i, π i * P i j = π j)
    (hG : IsGroupInverse (1 - P) G) (target start : ι) :
    trajectoryLawAfterStepCostColimit P hP target start =
      groupInverseReturnAdjustedPotential π G start target := by
  change sSup (Set.range (fun horizon =>
    ∫ path, pathFirstPassageAfterStepCost target horizon start path ∂
      finiteTrajectorySuccessorLaw P hP horizon start)) = _
  exact trajectoryLaw_afterStepCost_sup_eq_groupInverseReturnAdjustedPotential
    P G π hP hPpos hπnonneg hπsum hπstat hG target start

end InfoGeometry.QuantumContext.FiniteMarkovReturnTrajectoryColimit

end noncomputable section
