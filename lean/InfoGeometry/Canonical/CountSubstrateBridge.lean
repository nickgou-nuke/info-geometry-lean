import InfoGeometry.KL.Finite
import InfoGeometry.Canonical.ChiralAnomaly
import InfoGeometry.Canonical.HolographicEmergence

/-!
# Research.CountSubstrateBridge

Constructive count-first bridge:

- empirical counts induce a normalized probability state
- the induced probability state can be paired with the existing
  holographic-emergence theorem package

No new axioms are introduced.
-/

namespace InfoGeometry.Canonical.CountSubstrateBridge

open InfoGeometry
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
open InfoGeometry.Twistor

section CountsToProbability

variable {α : Type*} [Fintype α]

/-- Count substrate: empirical event counts. -/
abbrev CountSubstrate (α : Type*) := EmpiricalCounts α

/-- Nontrivial sampling hypothesis (at least one observed event). -/
abbrev CountSubstrateNontrivial {α : Type*} [Fintype α] (N : CountSubstrate α) : Prop :=
  EmpiricalNontrivial N

/-- Canonical empirical probability state induced by counts. -/
noncomputable def empiricalProbabilityState {α : Type*} [Fintype α]
    (N : CountSubstrate α) (hN : CountSubstrateNontrivial N) :
    ProbabilityDist α :=
  empiricalProbDist N hN

/-- Theorem `empiricalProbabilityState_spec`. -/
theorem empiricalProbabilityState_spec {α : Type*} [Fintype α]
    (N : CountSubstrate α) (hN : CountSubstrateNontrivial N) :
    ∀ x : α, empiricalProbabilityState N hN x = empiricalDistribution N x :=
  fun _ => rfl

/-- Theorem `exists_empiricalProbabilityState`. -/
theorem exists_empiricalProbabilityState {α : Type*} [Fintype α]
    (N : CountSubstrate α) (hN : CountSubstrateNontrivial N) :
    ∃ P : ProbabilityDist α, ∀ x : α, P x = empiricalDistribution N x :=
  ⟨empiricalProbabilityState N hN, fun _ => rfl⟩

end CountsToProbability

section CountsToHolographic

variable (n : Nat)
variable {α : Type*} {X : Type*}
  [Fintype α]
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X] [FiniteDimensional ℝ X]

/--
Count-first holographic package:
from nontrivial empirical counts we construct an empirical probability state,
then pair it with the existing constructive holographic-emergence chain.
-/
theorem countsFirst_holographicEmergence_package
    (N : CountSubstrate α)
    (hN : CountSubstrateNontrivial N)
    (Tflow : SinkhornTrajectory n)
    (CI : ConformalInference X)
    (hAnom : CI.chiralAnomalyOperator ≠ 0)
    (Tw : TwistedInference X)
    (L : BayesianLoop X)
    (IST : InfoSpectralTriple X)
    (Q : QuadraticForm ℝ (DoubledSpace X))
    (v : UnnormalizedProjectiveState (E := X))
    (hNull : IsVacuumApexNull (E := X) Q v) :
    ∃ P : ProbabilityDist α,
      (∀ x : α, P x = empiricalDistribution N x)
        ∧ EmergentTimeFlow n Tflow
        ∧ AnomalyScalePhase CI
        ∧ UpdateOrderPathDependent Tw.dual.nabla
        ∧ (∃ (M : Coupling 2)
            (hrow : HasPositiveRowSums 2 M)
            (hcolRow : HasPositiveColSums 2 (rowNormalize 2 M hrow))
            (hcol : HasPositiveColSums 2 M)
            (hrowCol : HasPositiveRowSums 2 (colNormalize 2 M hcol)),
            UpdateOrderHysteresis 2 M hrow hcolRow hcol hrowCol)
        ∧ AnomalyInflowClosure (E := X) L IST
        ∧ (∃ t : DoubledTwistorSpace (E := X) Q, t = vacuumApexTwistor (E := X) Q v hNull) := by
  refine ⟨empiricalProbabilityState N hN, ?_, ?_⟩
  · exact fun _ => rfl
  · exact holographicEmergence_package (n := n)
      (Tflow := Tflow) (CI := CI) (hAnom := hAnom) (Tw := Tw)
      (L := L) (IST := IST) (Q := Q) (v := v) (hNull := hNull)

end CountsToHolographic

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

/-- Lemma `rowNormalize_entrywisePositive`. -/
lemma rowNormalize_entrywisePositive
    {M : SinkhornMatrix n}
    (hM : EntrywisePositive n M)
    (hrow : HasPositiveRowSums n M) :
    EntrywisePositive n (rowNormalize n M hrow) := by
  intro i j
  unfold rowNormalize
  exact div_pos (hM i j) (hrow i)

/-- Lemma `colNormalize_entrywisePositive`. -/
lemma colNormalize_entrywisePositive
    {M : SinkhornMatrix n}
    (hM : EntrywisePositive n M)
    (hcol : HasPositiveColSums n M) :
    EntrywisePositive n (colNormalize n M hcol) := by
  intro i j
  unfold colNormalize
  exact div_pos (hM i j) (hcol j)

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

/-- Matrix trajectory component extracted from the positive iterate state. -/
noncomputable def countInducedIterate (k : Nat) : SinkhornMatrix n :=
  (countInducedPositiveIterate (n := n) N k).M

/-- Lemma `countInducedIterate_entrywisePositive`. -/
lemma countInducedIterate_entrywisePositive (k : Nat) :
    EntrywisePositive n (countInducedIterate (n := n) N k) :=
  (countInducedPositiveIterate (n := n) N k).pos

/-- Lemma `countInducedCoupling_hasPositiveRowSums`. -/
lemma countInducedCoupling_hasPositiveRowSums :
    HasPositiveRowSums n (countInducedCoupling n N) := by
  exact entrywisePositive_hasPositiveRowSums (n := n)
    (countInducedCoupling_entrywisePositive (n := n) (N := N))

/-- Lemma `countInducedCoupling_hasPositiveColSums`. -/
lemma countInducedCoupling_hasPositiveColSums :
    HasPositiveColSums n (countInducedCoupling n N) := by
  exact entrywisePositive_hasPositiveColSums (n := n)
    (countInducedCoupling_entrywisePositive (n := n) (N := N))

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

section CountsToHolographicDerivedFlow

variable (n : Nat)
variable {X : Type*}
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X] [FiniteDimensional ℝ X]

/--
Count-first holographic package with derived flow:
the trajectory input is eliminated and replaced by the canonical
count-induced Sinkhorn iterate trajectory.
-/
theorem countsFirst_holographicEmergence_of_countInducedTrajectory
    (N : CountSubstrate (Fin n))
    (hN : CountSubstrateNontrivial N)
    (CI : ConformalInference X)
    (hAnom : CI.chiralAnomalyOperator ≠ 0)
    (Tw : TwistedInference X)
    (L : BayesianLoop X)
    (IST : InfoSpectralTriple X)
    (Q : QuadraticForm ℝ (DoubledSpace X))
    (v : UnnormalizedProjectiveState (E := X))
    (hNull : IsVacuumApexNull (E := X) Q v) :
    ∃ P : ProbabilityDist (Fin n),
      (∀ x : Fin n, P x = empiricalDistribution N x)
        ∧ EmergentTimeFlow n (countInducedSinkhornTrajectory (n := n) N)
        ∧ AnomalyScalePhase CI
        ∧ UpdateOrderPathDependent Tw.dual.nabla
        ∧ (∃ (M : Coupling 2)
            (hrow2 : HasPositiveRowSums 2 M)
            (hcolRow2 : HasPositiveColSums 2 (rowNormalize 2 M hrow2))
            (hcol2 : HasPositiveColSums 2 M)
            (hrowCol2 : HasPositiveRowSums 2 (colNormalize 2 M hcol2)),
            UpdateOrderHysteresis 2 M hrow2 hcolRow2 hcol2 hrowCol2)
        ∧ AnomalyInflowClosure (E := X) L IST
        ∧ (∃ t : DoubledTwistorSpace (E := X) Q, t = vacuumApexTwistor (E := X) Q v hNull) := by
  exact countsFirst_holographicEmergence_package (n := n)
    (N := N) (hN := hN)
    (Tflow := countInducedSinkhornTrajectory (n := n) N)
    (CI := CI) (hAnom := hAnom) (Tw := Tw)
    (L := L) (IST := IST) (Q := Q) (v := v) (hNull := hNull)

end CountsToHolographicDerivedFlow

end InfoGeometry.Canonical.CountSubstrateBridge
