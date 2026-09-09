import InfoGeometry.GrandCanonical.Core

/-!
# Finite partition/cumulant readback

This file exposes the existing finite exponential-family theorems through a
semantics-neutral partition interface.  The carrier function may later be
interpreted as energy or surprisal; this owner does not identify those
interpretations.
-/

namespace InfoGeometry.Canonical.FinitePartitionCumulantReadback

open InfoGeometry.GrandCanonical

variable {α : Type*} [Fintype α] [Nonempty α]

def canonicalParams (k : α → ℝ) : GrandCanonicalParams α :=
  { energy := k }

noncomputable abbrev partitionFunction (k : α → ℝ) (β : ℝ) : ℝ :=
  GrandCanonical.partition (canonicalParams k) β

noncomputable abbrev logPartition (k : α → ℝ) (β : ℝ) : ℝ :=
  GrandCanonical.potential (canonicalParams k) β

theorem partitionFunction_pos (k : α → ℝ) (β : ℝ) :
    0 < partitionFunction k β := by
  exact GrandCanonical.partition_pos (canonicalParams k) β

theorem logPartition_deriv_eq_neg_mean (k : α → ℝ) (β : ℝ) :
    deriv (logPartition k) β = -GrandCanonical.mean (canonicalParams k) β := by
  exact GrandCanonical.potential_deriv_eq_neg_mean (canonicalParams k) β

theorem logPartition_second_deriv_eq_variance (k : α → ℝ) (β : ℝ) :
    GrandCanonical.hessian (canonicalParams k) β =
      GrandCanonical.variance (canonicalParams k) β := by
  exact GrandCanonical.potential_second_derivative_eq_variance (canonicalParams k) β

theorem variance_nonneg (k : α → ℝ) (β : ℝ) :
    0 ≤ GrandCanonical.variance (canonicalParams k) β := by
  exact GrandCanonical.variance_nonneg (canonicalParams k) β

/-- The surprisal coordinates associated with a strictly positive finite law. -/
noncomputable def surprisal (p : α → ℝ) : α → ℝ :=
  fun x => -Real.log (p x)

omit [Nonempty α] in
/-- At the normalization order, the surprisal partition function is one. -/
lemma surprisal_partition_one
    (p : α → ℝ) (hp : ∀ x, 0 < p x) (hsum : ∑ x, p x = 1) :
    partitionFunction (surprisal p) 1 = 1 := by
  unfold partitionFunction GrandCanonical.partition surprisal
  have hterm (x : α) :
      Real.exp (-1 * (-Real.log (p x))) = p x := by
    rw [show -1 * (-Real.log (p x)) = Real.log (p x) by ring]
    exact Real.exp_log (hp x)
  calc
    (∑ x, Real.exp (-1 * (-Real.log (p x)))) = ∑ x, p x := by
      apply Finset.sum_congr rfl
      intro x hx
      exact hterm x
    _ = 1 := hsum

omit [Nonempty α] in
/-- The normalized mean of finite surprisal is the Shannon readout. -/
lemma mean_surprisal_at_one
    (p : α → ℝ) (hp : ∀ x, 0 < p x) (hsum : ∑ x, p x = 1) :
    GrandCanonical.mean (canonicalParams (surprisal p)) 1 =
      ∑ x, p x * (-Real.log (p x)) := by
  unfold GrandCanonical.mean GrandCanonical.gibbsWeight
  have hterm (x : α) :
      Real.exp (-1 * (-Real.log (p x))) = p x := by
    rw [show -1 * (-Real.log (p x)) = Real.log (p x) by ring]
    exact Real.exp_log (hp x)
  have hZ' : partitionFunction (surprisal p) 1 = 1 :=
    surprisal_partition_one p hp hsum
  have hZ'' : GrandCanonical.partition (canonicalParams (surprisal p)) 1 = 1 := hZ'
  apply Finset.sum_congr rfl
  intro x hx
  change Real.exp (-1 * (canonicalParams (surprisal p)).energy x) /
      GrandCanonical.partition (canonicalParams (surprisal p)) 1 *
        (canonicalParams (surprisal p)).energy x = p x * -Real.log (p x)
  rw [show (canonicalParams (surprisal p)).energy x = -Real.log (p x) by rfl,
    hZ'', div_one, hterm]

omit [Nonempty α] in
/-- Finite Shannon entropy as the expectation of surprisal. -/
noncomputable def shannonEntropy (p : α → ℝ) : ℝ :=
  ∑ x, p x * (-Real.log (p x))

/-- The log-partition derivative at order one is minus Shannon entropy. -/
lemma logPartition_deriv_surprisal_at_one
    (p : α → ℝ) (hp : ∀ x, 0 < p x) (hsum : ∑ x, p x = 1) :
    deriv (logPartition (surprisal p)) 1 = -shannonEntropy p := by
  rw [logPartition_deriv_eq_neg_mean]
  have hmean := mean_surprisal_at_one p hp hsum
  simp only [shannonEntropy]
  rw [hmean]

lemma logPartition_second_deriv_surprisal_at_one
    (p : α → ℝ) :
    GrandCanonical.hessian (canonicalParams (surprisal p)) 1 =
      GrandCanonical.variance (canonicalParams (surprisal p)) 1 := by
  exact logPartition_second_deriv_eq_variance (surprisal p) 1

lemma surprisal_variance_nonneg
    (p : α → ℝ) :
    0 ≤ GrandCanonical.variance (canonicalParams (surprisal p)) 1 := by
  exact variance_nonneg (surprisal p) 1

omit [Nonempty α] in
/-- The finite Gibbs variance at order one is the varentropy of `p`. -/
lemma surprisal_variance_eq_varentropy
    (p : α → ℝ) (hp : ∀ x, 0 < p x) (hsum : ∑ x, p x = 1) :
    GrandCanonical.variance (canonicalParams (surprisal p)) 1 =
      ∑ x, p x * ((-Real.log (p x)) -
        (∑ y, p y * (-Real.log (p y)))) ^ (2 : ℕ) := by
  unfold GrandCanonical.variance
  have hmean : GrandCanonical.mean (canonicalParams (surprisal p)) 1 =
      ∑ y, p y * (-Real.log (p y)) :=
    mean_surprisal_at_one p hp hsum
  rw [hmean]
  apply Finset.sum_congr rfl
  intro x hx
  have hweight : GrandCanonical.gibbsWeight
      (canonicalParams (surprisal p)) 1 x = p x := by
    unfold GrandCanonical.gibbsWeight
    change Real.exp (-1 * (-Real.log (p x))) /
      GrandCanonical.partition (canonicalParams (surprisal p)) 1 = p x
    rw [show -1 * (-Real.log (p x)) = Real.log (p x) by ring]
    rw [Real.exp_log (hp x)]
    have hZ : GrandCanonical.partition (canonicalParams (surprisal p)) 1 = 1 :=
      surprisal_partition_one p hp hsum
    rw [hZ]
    simp
  rw [hweight]
  rfl

omit [Nonempty α] in
lemma surprisal_partition_two
    (p : α → ℝ) (hp : ∀ x, 0 < p x) :
    partitionFunction (surprisal p) 2 = ∑ x, (p x) ^ 2 := by
  unfold partitionFunction GrandCanonical.partition
  apply Finset.sum_congr rfl
  intro x hx
  change Real.exp (-2 * (-Real.log (p x))) = p x ^ 2
  rw [show -(2 : ℝ) * (-Real.log (p x)) =
      Real.log (p x) + Real.log (p x) by ring]
  simp [Real.exp_add, Real.exp_log (hp x), pow_two]

end InfoGeometry.Canonical.FinitePartitionCumulantReadback
