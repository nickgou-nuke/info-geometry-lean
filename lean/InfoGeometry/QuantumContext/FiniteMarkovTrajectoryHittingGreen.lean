/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.QuantumContext.FiniteMarkovTrajectorySuccessorLaw
import InfoGeometry.QuantumContext.FiniteMarkovHittingExpectationGreen
import InfoGeometry.QuantumContext.FiniteMarkovDirichletOrderColimit

/-!
# Finite trajectory Green expectation bridge

Transports the existing finite successor-path cost through the production
trajectory kernel's successor-coordinate pushforward. The horizon supremum
remains a supremum of finite-horizon integrals.
-/

namespace InfoGeometry.QuantumContext.FiniteMarkovTrajectoryHittingGreen

open MeasureTheory
open ProbabilityTheory
open CategoryTheory
open CategoryTheory.Limits
open InfoGeometry.Categorical.InductivePosetColimit
open InfoGeometry.QuantumContext.FiniteMarkovTrajectorySuccessorLaw
open InfoGeometry.QuantumContext.FiniteMarkovHittingPMFExpectation
open InfoGeometry.QuantumContext.FiniteMarkovHittingExpectationGreen
open InfoGeometry.QuantumContext.FiniteMarkovDirichletApproximation
open InfoGeometry.QuantumContext.FiniteMarkovDirichletOrderColimit
open InfoGeometry.QuantumContext.FiniteMarkovHittingColimitGreen
open InfoGeometry.QuantumContext.MarkovDrazin
open InfoGeometry.Canonical.HartwigSouriauFrameDrazin

open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

local instance : MeasurableSpace ι := ⊤
local instance : MeasurableSingletonClass ι := inferInstance

section PMFExpectationSpace

local instance (n : ℕ) : MeasurableSpace (Fin n → ι) := ⊤
local instance (n : ℕ) : MeasurableSingletonClass (Fin n → ι) := inferInstance

private theorem successorPathExpectedCost_eq_sum
    (P : Matrix ι ι ℝ) (hP : P ∈ Matrix.rowStochastic ℝ ι)
    (target i : ι) (n : ℕ) :
    successorPathExpectedCost P hP target n i =
      ∑ path, (successorPathPMF P hP n i path).toReal *
        pathFirstHitCost target n i path := by
  unfold successorPathExpectedCost
  rw [PMF.integral_eq_sum]
  simp only [smul_eq_mul]

end PMFExpectationSpace

/-- The finite first-hit path-cost integral under the production trajectory
kernel's successor-coordinate pushforward is the existing recursive PMF
expectation. -/
theorem trajectoryLaw_integral_pathFirstHitCost_eq_successorPathExpectedCost
    (P : Matrix ι ι ℝ) (hP : P ∈ Matrix.rowStochastic ℝ ι)
    (target i : ι) (n : ℕ) :
    (∫ path, pathFirstHitCost target n i path ∂
      finiteTrajectorySuccessorLaw P hP n i) =
      successorPathExpectedCost P hP target n i := by
  rw [finiteTrajectorySuccessorLaw_eq_successorPathPMF_toMeasure]
  calc
    (∫ path, pathFirstHitCost target n i path ∂
      (successorPathPMF P hP n i).toMeasure) =
        ∑ path, (successorPathPMF P hP n i path).toReal *
          pathFirstHitCost target n i path := by
            rw [PMF.integral_eq_sum]
            simp only [smul_eq_mul]
    _ = successorPathExpectedCost P hP target n i :=
      (successorPathExpectedCost_eq_sum P hP target i n).symm

/-- At each finite horizon, the production trajectory-law integral is the
existing Bellman approximant. This identifies the production stages with the
objects of the established real-preorder diagram. -/
theorem trajectoryLaw_integral_pathFirstHitCost_eq_firstHitApproximation
    (P : Matrix ι ι ℝ) (hP : P ∈ Matrix.rowStochastic ℝ ι)
    (target i : ι) (n : ℕ) :
    (∫ path, pathFirstHitCost target n i path ∂
      finiteTrajectorySuccessorLaw P hP n i) =
      firstHitApproximation P target n i := by
  rw [trajectoryLaw_integral_pathFirstHitCost_eq_successorPathExpectedCost]
  exact successorPathExpectedCost_eq_firstHitApproximation P hP target n i

/-- The finite-horizon production trajectory costs are monotone in the
horizon, by transport from the Bellman approximants. -/
theorem trajectoryLaw_hittingCost_mono
    (P : Matrix ι ι ℝ) (hP : P ∈ Matrix.rowStochastic ℝ ι)
    (target i : ι) (n : ℕ) :
    (∫ path, pathFirstHitCost target n i path ∂
      finiteTrajectorySuccessorLaw P hP n i) ≤
      ∫ path, pathFirstHitCost target (n + 1) i path ∂
        finiteTrajectorySuccessorLaw P hP (n + 1) i := by
  rw [trajectoryLaw_integral_pathFirstHitCost_eq_firstHitApproximation,
    trajectoryLaw_integral_pathFirstHitCost_eq_firstHitApproximation]
  exact firstHitApproximation_mono P hP target n i

/-- The finite-horizon costs of the production trajectory law, viewed as a
diagram in the preorder category of real values. -/
noncomputable def trajectoryLawHittingCostDiagram
    (P : Matrix ι ι ℝ) (hP : P ∈ Matrix.rowStochastic ℝ ι)
    (target i : ι) : ℕ ⥤ ℝ :=
  Functor.ofSequence (fun n =>
    homOfLE (trajectoryLaw_hittingCost_mono P hP target i n))

/-- The production-law and Bellman diagrams have the same stage values, hence
the same object range in the real preorder. -/
theorem trajectoryLawHittingCostDiagram_range_eq
    (P : Matrix ι ι ℝ) (hP : P ∈ Matrix.rowStochastic ℝ ι)
    (target i : ι) :
    Set.range (trajectoryLawHittingCostDiagram P hP target i).obj =
      Set.range (firstHitApproximationDiagram P hP target i).obj := by
  ext y
  constructor
  · rintro ⟨n, rfl⟩
    refine ⟨n, ?_⟩
    simpa [trajectoryLawHittingCostDiagram, firstHitApproximationDiagram] using
      (trajectoryLaw_integral_pathFirstHitCost_eq_firstHitApproximation
        P hP target i n).symm
  · rintro ⟨n, rfl⟩
    refine ⟨n, ?_⟩
    simpa [trajectoryLawHittingCostDiagram, firstHitApproximationDiagram] using
      trajectoryLaw_integral_pathFirstHitCost_eq_firstHitApproximation
        P hP target i n

/-- Under strict positivity, the production trajectory-law diagram has the
same least-upper-bound colimit as the existing Bellman diagram. -/
theorem trajectoryLawHittingCostColimit_isLUB
    (P : Matrix ι ι ℝ) (hP : P ∈ Matrix.rowStochastic ℝ ι)
    (hPpos : ∀ i j, 0 < P i j) (target i : ι) :
    IsLUB (Set.range (trajectoryLawHittingCostDiagram P hP target i).obj)
      (firstHitApproximationColimit P hP target i) := by
  rw [trajectoryLawHittingCostDiagram_range_eq P hP target i]
  obtain ⟨ε, hε, hminor⟩ := exists_target_minorization_of_positive P target hPpos
  exact firstHitApproximationColimit_isLUB P hP target ε hε hminor i

/-- Strict positivity makes the real-preorder colimit cocone of the production
trajectory-law costs available. Its vertex is the existing Bellman order
colimit; no path-space limit is introduced. -/
noncomputable def trajectoryLawHittingCostColimitCocone
    (P : Matrix ι ι ℝ) (hP : P ∈ Matrix.rowStochastic ℝ ι)
    (hPpos : ∀ i j, 0 < P i j) (target i : ι) :
    ColimitCocone (trajectoryLawHittingCostDiagram P hP target i) :=
  colimitCoconeOfIsLUB
    (trajectoryLawHittingCostDiagram P hP target i)
    (trajectoryLawHittingCostColimit_isLUB P hP hPpos target i)

/-- The supremum of finite-horizon first-hit costs integrated against the
production trajectory law is the already established group-inverse potential
difference. This statement is only about finite-horizon integrals and their
order supremum. -/
theorem trajectoryLaw_hittingCost_sup_eq_groupInversePotentialDifference
    [Nonempty ι]
    (P G : Matrix ι ι ℝ) (π : ι → ℝ)
    (hP : P ∈ Matrix.rowStochastic ℝ ι)
    (hPpos : ∀ i j, 0 < P i j)
    (hπnonneg : ∀ i, 0 ≤ π i)
    (hπsum : ∑ i, π i = 1)
    (hπstat : ∀ j, ∑ i, π i * P i j = π j)
    (hG : IsGroupInverse (1 - P) G)
    (target i : ι) :
    sSup (Set.range (fun n =>
      ∫ path, pathFirstHitCost target n i path ∂
        finiteTrajectorySuccessorLaw P hP n i)) =
      groupInversePotentialDifference π G i target := by
  have hcost : (fun n =>
      ∫ path, pathFirstHitCost target n i path ∂
        finiteTrajectorySuccessorLaw P hP n i) =
      fun n => successorPathExpectedCost P hP target n i := by
    funext n
    exact trajectoryLaw_integral_pathFirstHitCost_eq_successorPathExpectedCost
      P hP target i n
  rw [hcost]
  exact successorPathExpectedCost_sup_eq_groupInversePotentialDifference
    P G π hP hPpos hπnonneg hπsum hπstat hG target i

/-- The stationary-weighted sum over targets of the production trajectory
law's finite-horizon hitting costs has order colimit `trace G`. This is a
colimit of finite sums and finite-horizon integrals; it does not assert an
infinite-path expectation or a limit of transition iterates. -/
theorem trajectoryLaw_weightedHittingCostColimit_eq_groupInverseTrace
    [Nonempty ι]
    (P G : Matrix ι ι ℝ) (π : ι → ℝ)
    (hP : P ∈ Matrix.rowStochastic ℝ ι)
    (hPpos : ∀ i j, 0 < P i j)
    (hπnonneg : ∀ i, 0 ≤ π i)
    (hπsum : ∑ i, π i = 1)
    (hπstat : ∀ j, ∑ i, π i * P i j = π j)
    (hG : IsGroupInverse (1 - P) G)
    (i : ι) :
    sSup (Set.range (fun n =>
      ∑ target ∈ Finset.univ, π target *
        ∫ path, pathFirstHitCost target n i path ∂
          finiteTrajectorySuccessorLaw P hP n i)) = Matrix.trace G := by
  classical
  have hminorExists : ∀ target, ∃ ε : ℝ, 0 < ε ∧ ∀ state, ε ≤ P state target := by
    intro target
    exact exists_target_minorization_of_positive P target hPpos
  choose ε hε hminor using hminorExists
  let cost : ℕ → ι → ℝ := fun n target =>
    ∫ path, pathFirstHitCost target n i path ∂
      finiteTrajectorySuccessorLaw P hP n i
  let upper : ι → ℝ := fun target => (ε target)⁻¹
  have hcostMono (target : ι) : Monotone (fun n => cost n target) := by
    apply monotone_nat_of_le_succ
    intro n
    exact trajectoryLaw_hittingCost_mono P hP target i n
  have hcostBound (n : ℕ) (target : ι) : cost n target ≤ upper target := by
    rw [show cost n target = firstHitApproximation P target n i by
      exact trajectoryLaw_integral_pathFirstHitCost_eq_firstHitApproximation
        P hP target i n]
    exact firstHitApproximation_le_inv_of_target_minorization
      P hP target (ε target) (hε target) (hminor target) n i
  have hcostBdd (target : ι) : BddAbove (Set.range (fun n => cost n target)) := by
    refine ⟨upper target, ?_⟩
    rintro y ⟨n, rfl⟩
    exact hcostBound n target
  have hweightedSup := csSup_range_weighted_finset_sum_of_monotone
    Finset.univ π cost hπnonneg hcostMono upper hcostBound
  rw [show (fun n =>
      ∑ target ∈ Finset.univ, π target *
        ∫ path, pathFirstHitCost target n i path ∂
          finiteTrajectorySuccessorLaw P hP n i) =
        fun n => ∑ target ∈ Finset.univ, π target * cost n target from rfl,
    hweightedSup]
  calc
    (∑ target ∈ Finset.univ,
        sSup (Set.range (fun n => π target * cost n target))) =
      ∑ target ∈ Finset.univ,
        π target * groupInversePotentialDifference π G i target := by
          apply Finset.sum_congr rfl
          intro target htarget
          rw [csSup_range_mul_left_of_nonneg
            (π target) (hπnonneg target) (fun n => cost n target)
            (hcostBdd target)]
          rw [trajectoryLaw_hittingCost_sup_eq_groupInversePotentialDifference
            P G π hP hPpos hπnonneg hπsum hπstat hG target i]
    _ = Matrix.trace G :=
      markovGroupInverse_weightedPotentialSum_eq_trace
        P G π hP hG
        (fun target =>
          (stationaryRowProbability_pos_of_pos_entries
            P π hPpos hπnonneg hπsum hπstat target).ne') i

/-- The nonnegative-weighted finite-horizon trajectory costs are monotone in
the horizon. -/
theorem trajectoryLaw_weightedHittingCost_mono
    (P : Matrix ι ι ℝ) (hP : P ∈ Matrix.rowStochastic ℝ ι)
    (π : ι → ℝ) (hπnonneg : ∀ j, 0 ≤ π j) (targetStart : ι)
    (n : ℕ) :
    (∑ target ∈ Finset.univ, π target *
      ∫ path, pathFirstHitCost target n targetStart path ∂
        finiteTrajectorySuccessorLaw P hP n targetStart) ≤
    ∑ target ∈ Finset.univ, π target *
      ∫ path, pathFirstHitCost target (n + 1) targetStart path ∂
        finiteTrajectorySuccessorLaw P hP (n + 1) targetStart := by
  apply Finset.sum_le_sum
  intro target htarget
  exact mul_le_mul_of_nonneg_left
    (trajectoryLaw_hittingCost_mono P hP target targetStart n)
    (hπnonneg target)

/-- Strict positivity bounds the nonnegative-weighted finite-horizon costs,
using a separate positive minorization for each possible target. -/
theorem trajectoryLaw_weightedHittingCost_bddAbove
    (P : Matrix ι ι ℝ) (hP : P ∈ Matrix.rowStochastic ℝ ι)
    (hPpos : ∀ i j, 0 < P i j) (π : ι → ℝ)
    (hπnonneg : ∀ j, 0 ≤ π j) (targetStart : ι) :
    BddAbove (Set.range (fun n =>
      ∑ target ∈ Finset.univ, π target *
        ∫ path, pathFirstHitCost target n targetStart path ∂
          finiteTrajectorySuccessorLaw P hP n targetStart)) := by
  classical
  have hminorExists : ∀ target, ∃ ε : ℝ, 0 < ε ∧ ∀ state, ε ≤ P state target := by
    intro target
    exact exists_target_minorization_of_positive P target hPpos
  choose ε hε hminor using hminorExists
  refine ⟨∑ target ∈ Finset.univ, π target * (ε target)⁻¹, ?_⟩
  rintro y ⟨n, rfl⟩
  apply Finset.sum_le_sum
  intro target htarget
  apply mul_le_mul_of_nonneg_left _ (hπnonneg target)
  rw [trajectoryLaw_integral_pathFirstHitCost_eq_firstHitApproximation]
  exact firstHitApproximation_le_inv_of_target_minorization
    P hP target (ε target) (hε target) (hminor target) n targetStart

/-- The nonnegative-weighted finite-horizon production trajectory costs form a
diagram in the real preorder category. -/
noncomputable def trajectoryLawWeightedHittingCostDiagram
    (P : Matrix ι ι ℝ) (hP : P ∈ Matrix.rowStochastic ℝ ι)
    (π : ι → ℝ) (hπnonneg : ∀ j, 0 ≤ π j) (targetStart : ι) : ℕ ⥤ ℝ :=
  Functor.ofSequence (fun n =>
    homOfLE (trajectoryLaw_weightedHittingCost_mono
      P hP π hπnonneg targetStart n))

/-- The real-preorder least-upper-bound colimit of the weighted aggregate
trajectory costs. -/
theorem trajectoryLawWeightedHittingCostColimit_isLUB
    (P : Matrix ι ι ℝ) (hP : P ∈ Matrix.rowStochastic ℝ ι)
    (hPpos : ∀ i j, 0 < P i j) (π : ι → ℝ)
    (hπnonneg : ∀ j, 0 ≤ π j) (targetStart : ι) :
    IsLUB
      (Set.range (trajectoryLawWeightedHittingCostDiagram
        P hP π hπnonneg targetStart).obj)
      (sSup (Set.range (trajectoryLawWeightedHittingCostDiagram
        P hP π hπnonneg targetStart).obj)) := by
  apply isLUB_csSup
  · exact ⟨_, ⟨0, rfl⟩⟩
  · exact trajectoryLaw_weightedHittingCost_bddAbove
      P hP hPpos π hπnonneg targetStart

/-- The weighted aggregate trajectory-cost diagram has its canonical
real-preorder colimit cocone, built by the repository's LUB-to-colimit owner. -/
noncomputable def trajectoryLawWeightedHittingCostColimitCocone
    (P : Matrix ι ι ℝ) (hP : P ∈ Matrix.rowStochastic ℝ ι)
    (hPpos : ∀ i j, 0 < P i j) (π : ι → ℝ)
    (hπnonneg : ∀ j, 0 ≤ π j) (targetStart : ι) :
    ColimitCocone (trajectoryLawWeightedHittingCostDiagram
      P hP π hπnonneg targetStart) :=
  colimitCoconeOfIsLUB
    (trajectoryLawWeightedHittingCostDiagram P hP π hπnonneg targetStart)
    (trajectoryLawWeightedHittingCostColimit_isLUB
      P hP hPpos π hπnonneg targetStart)

end InfoGeometry.QuantumContext.FiniteMarkovTrajectoryHittingGreen
