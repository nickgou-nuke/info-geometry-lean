import InfoGeometry.Canonical.CountProbabilityState
import InfoGeometry.Canonical.SinkhornFoundation

namespace InfoGeometry.Canonical.CountSubstrateBridge

open InfoGeometry.Canonical.MoE

section CountInducedFlow

variable (n : Nat)
variable (N : CountSubstrate (Fin n))

/-- Entrywise positivity predicate for Sinkhorn matrices. -/
def EntrywisePositive (M : SinkhornMatrix n) : Prop :=
  ∀ i j : Fin n, 0 < M i j

/-- Pseudocount-smoothed nonnegative weight from empirical counts. -/
noncomputable def countWeight (i : Fin n) : ℝ :=
  (N i : ℝ) + 1

/-- Positivity of the pseudocount-smoothed empirical weight. -/
lemma countWeight_pos (i : Fin n) : 0 < countWeight n N i := by
  unfold countWeight
  positivity

/-- Rank-one count-induced coupling. -/
noncomputable def countInducedCoupling : Coupling n :=
  fun i j => countWeight n N i * countWeight n N j

/-- The count-induced coupling is entrywise positive. -/
lemma countInducedCoupling_entrywisePositive :
    EntrywisePositive n (countInducedCoupling n N) := by
  intro i j
  unfold countInducedCoupling
  exact mul_pos (countWeight_pos (n := n) (N := N) i) (countWeight_pos (n := n) (N := N) j)

/-- Entrywise positivity forces positive row sums. -/
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

/-- Entrywise positivity forces positive column sums. -/
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

/-- Matrix together with an entrywise-positivity property. -/
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
            rowNormalize_entrywisePositive Sk.pos hrow⟩
      | .col =>
          let hcol : HasPositiveColSums n Sk.M :=
            entrywisePositive_hasPositiveColSums (n := n) Sk.pos
          ⟨colNormalize n Sk.M hcol,
            colNormalize_entrywisePositive Sk.pos hcol⟩
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

/-- Every count-induced Sinkhorn iterate remains entrywise positive. -/
lemma countInducedIterate_entrywisePositive (k : Nat) :
    EntrywisePositive n (countInducedIterate (n := n) N k) := by
  exact (countInducedPositiveIterate (n := n) N k).pos

/-- Every count-induced Sinkhorn iterate has positive row sums. -/
lemma countInducedIterate_hasPositiveRowSums (k : Nat) :
    HasPositiveRowSums n (countInducedIterate (n := n) N k) := by
  exact entrywisePositive_hasPositiveRowSums (n := n)
    (countInducedIterate_entrywisePositive (n := n) N k)

/-- Every count-induced Sinkhorn iterate has positive column sums. -/
lemma countInducedIterate_hasPositiveColSums (k : Nat) :
    HasPositiveColSums n (countInducedIterate (n := n) N k) := by
  exact entrywisePositive_hasPositiveColSums (n := n)
    (countInducedIterate_entrywisePositive (n := n) N k)

/-- Stepwise Sinkhorn law for the count-induced iterate. -/
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

end CountInducedFlow

end InfoGeometry.Canonical.CountSubstrateBridge
