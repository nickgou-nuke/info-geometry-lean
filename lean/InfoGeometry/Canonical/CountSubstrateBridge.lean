import InfoGeometry.KL.Finite
import InfoGeometry.Canonical.ChiralAnomaly
import InfoGeometry.Canonical.HolographicEmergence

/-!
# Research.CountSubstrateBridge

Constructive count-first bridge:

- empirical counts induce a normalized probability state
- count-induced Sinkhorn trajectories provide a constructive flow

This module defines the mapping from empirical event counts to informational
dynamics. Vacuous zero-quadratic-form scaffolds have been removed.
-/

namespace InfoGeometry.Canonical.CountSubstrateBridge

open InfoGeometry
open InfoGeometry.Krein
open InfoGeometry.KL
open InfoGeometry.Canonical.MoE
open InfoGeometry.Canonical.ChiralAnomaly
open InfoGeometry.Canonical.HolographicEmergence
open InfoGeometry.Canonical.WeylInformationGauge
open InfoGeometry.Canonical.ConformalUnification
open InfoGeometry.Canonical.InformationTorsion
open InfoGeometry.Canonical.AnomalyInflow
open InfoGeometry.Canonical.TopologicalInvariants
open InfoGeometry.Canonical.ChiralTorsionBridge
open InfoGeometry.Canonical.SpectralInference

section CountsToProbability

variable {α : Type*} [Fintype α]

/-- Count substrate: empirical event counts. -/
abbrev CountSubstrate (α : Type*) := EmpiricalCounts α

/-- Nontrivial sampling hypothesis (at least one observed event). -/
abbrev CountSubstrateNontrivial {α : Type*} [Fintype α] (N : CountSubstrate α) : Prop :=
  empirical_nontrivial N

/-- Canonical empirical probability state induced by counts. -/
noncomputable def empiricalProbabilityState {α : Type*} [Fintype α]
    (N : CountSubstrate α) (hN : CountSubstrateNontrivial N) :
    ProbabilityDist α :=
  empirical_fin_prob N hN

/-- Theorem `empiricalProbabilityState_spec`. -/
theorem empiricalProbabilityState_spec {α : Type*} [Fintype α]
    (N : CountSubstrate α) (hN : CountSubstrateNontrivial N) :
    ∀ x : α, (empiricalProbabilityState N hN x).toReal = empirical_distribution N x := by
  intro x
  have htotal_pos : 0 < ∑ y, (N y : ℝ) := by
    exact_mod_cast hN
  have hratio_nonneg : 0 ≤ (N x : ℝ) / (∑ y, (N y : ℝ)) := by
    exact div_nonneg (Nat.cast_nonneg _) htotal_pos.le
  simp [empiricalProbabilityState, empirical_fin_prob, empirical_distribution,
    htotal_pos.ne', hratio_nonneg]

/-- Theorem `exists_empiricalProbabilityState`. -/
theorem exists_empiricalProbabilityState {α : Type*} [Fintype α]
    (N : CountSubstrate α) (hN : CountSubstrateNontrivial N) :
    ∃ P : ProbabilityDist α, ∀ x : α, (P x).toReal = empirical_distribution N x :=
  ⟨empiricalProbabilityState N hN, empiricalProbabilityState_spec N hN⟩

end CountsToProbability

section CountInducedFlow

variable (n : Nat)
variable (N : CountSubstrate (Fin n))

/-- Entrywise positivity predicate for Sinkhorn matrices. -/
def EntrywisePositive (M : SinkhornMatrix n) : Prop :=
  ∀ i j : Fin n, 0 < M i j

/-- Pseudocount-smoothed nonnegative weight from empirical counts. -/
noncomputable def countWeight (i : Fin n) : ℝ :=
  (N i : ℝ) + 1

/-- Lemma `countWeight_pos`. -/
lemma countWeight_pos (i : Fin n) : 0 < countWeight n N i := by
  unfold countWeight
  positivity

/--
Rank-one count-induced coupling:
`M(i,j) = ((N i)+1) * ((N j)+1)`.
-/
noncomputable def countInducedCoupling : Coupling n :=
  fun i j => countWeight n N i * countWeight n N j

/-- Lemma `countInducedCoupling_entrywisePositive`. -/
lemma countInducedCoupling_entrywisePositive :
    EntrywisePositive n (countInducedCoupling n N) := by
  intro i j
  unfold countInducedCoupling
  exact mul_pos (countWeight_pos (n := n) (N := N) i) (countWeight_pos (n := n) (N := N) j)

/-- Lemma `entrywisePositive_hasPositiveRowSums`. -/
lemma entrywisePositive_hasPositiveRowSums
    {M : SinkhornMatrix n}
    (hM : EntrywisePositive n M) :
    HasPositiveRowSums n M := by
  intro i
  unfold rowSum
  have hdiag : 0 < M i i := hM i i
  have hle : M i i ≤ ∑ j : Fin n, M i j := by
    exact Finset.single_le_sum (fun j _hj => (hM i j).le) (by simp)
  exact lt_of_lt_of_le hdiag hle

/-- Lemma `entrywisePositive_hasPositiveColSums`. -/
lemma entrywisePositive_hasPositiveColSums
    {M : SinkhornMatrix n}
    (hM : EntrywisePositive n M) :
    HasPositiveColSums n M := by
  intro j
  unfold colSum
  have hdiag : 0 < M j j := hM j j
  have hle : M j j ≤ ∑ i : Fin n, M i j := by
    exact Finset.single_le_sum (fun i _hi => (hM i j).le) (by simp)
  exact lt_of_lt_of_le hdiag hle

/-- Matrix together with an entrywise-positivity certificate. -/
structure PositiveSinkhornState where
  M : SinkhornMatrix n
  pos : EntrywisePositive n M

/-- Count-induced positive iterate state along alternating Sinkhorn phases. -/
noncomputable def countInducedPositiveIterate : Nat → PositiveSinkhornState n
  | 0 => ⟨countInducedCoupling n N, countInducedCoupling_entrywisePositive (n := n) (N := N)⟩
  | k + 1 =>
      let Sk := countInducedPositiveIterate k
      match phaseAt k with
      | .row =>
          let hrow : HasPositiveRowSums n Sk.M :=
            entrywisePositive_hasPositiveRowSums (n := n) Sk.pos
          ⟨rowNormalize n Sk.M hrow,
            rowNormalize_entrywisePositive (n := n) Sk.pos hrow⟩
      | .col =>
          let hcol : HasPositiveColSums n Sk.M :=
            entrywisePositive_hasPositiveColSums (n := n) Sk.pos
          ⟨colNormalize n Sk.M hcol,
            colNormalize_entrywisePositive (n := n) Sk.pos hcol⟩
where
  rowNormalize_entrywisePositive
      {M : SinkhornMatrix n}
      (hM : EntrywisePositive n M)
      (hrow : HasPositiveRowSums n M) :
      EntrywisePositive n (rowNormalize n M hrow) := by
    intro i j
    unfold rowNormalize
    exact div_pos (hM i j) (hrow i)
  colNormalize_entrywisePositive
      {M : SinkhornMatrix n}
      (hM : EntrywisePositive n M)
      (hcol : HasPositiveColSums n M) :
      EntrywisePositive n (colNormalize n M hcol) := by
    intro i j
    unfold colNormalize
    exact div_pos (hM i j) (hcol j)

/-- Matrix trajectory component extracted from the positive iterate state. -/
noncomputable def countInducedIterate (k : Nat) : SinkhornMatrix n :=
  (countInducedPositiveIterate (n := n) N k).M

/-- Lemma `countInducedIterate_step`. -/
lemma countInducedIterate_step (k : Nat) :
    SinkhornStep n (phaseAt k)
      (countInducedIterate (n := n) N k)
      (countInducedIterate (n := n) N (k + 1)) := by
  let Sk := countInducedPositiveIterate (n := n) N k
  cases hphase : phaseAt k with
  | row =>
      refine ⟨entrywisePositive_hasPositiveRowSums (n := n) (M := Sk.M) Sk.pos, ?_⟩
      simp [countInducedIterate, countInducedPositiveIterate, hphase]
  | col =>
      refine ⟨entrywisePositive_hasPositiveColSums (n := n) (M := Sk.M) Sk.pos, ?_⟩
      simp [countInducedIterate, countInducedPositiveIterate, hphase]

/--
Constructive Sinkhorn trajectory from the count-induced coupling,
using iterate-local positivity invariants.
-/
noncomputable def countInducedSinkhornTrajectory
    : SinkhornTrajectory n :=
  { state := countInducedIterate (n := n) N
    step := countInducedIterate_step (n := n) N }

/-- Theorem `emergentTimeFlow_countInducedSinkhornTrajectory`. -/
theorem emergentTimeFlow_countInducedSinkhornTrajectory
    :
    EmergentTimeFlow n (countInducedSinkhornTrajectory (n := n) N) := by
  exact emergentTimeFlow_of_sinkhornTrajectory (n := n)
    (countInducedSinkhornTrajectory (n := n) N)

end CountInducedFlow

end InfoGeometry.Canonical.CountSubstrateBridge
