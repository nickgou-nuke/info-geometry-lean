import InfoGeometry.PositiveMeasure -- canonical PositiveMeasure

namespace InfoGeometry.RegularizedKL
end InfoGeometry.RegularizedKL

open Finset
open InfoGeometry
open scoped BigOperators

/- Utility file capturing the “Path 2” regularization / Laplace smoothing
idea mentioned by the user.  We work in a finite, nonempty universe of
states and add a small positive vacuum energy `ε` to every count.  This
forces all induced probabilities to be strictly positive and therefore
avoids `log 0` singularities in the KL divergence. -/


namespace StatisticalMechanics

/--
The regularized partition function.  We add `ε` to every possible state,
inflating the total mass by `|α| * ε`.
-/
noncomputable def regTotalCount {α : Type*} [Fintype α] [Nonempty α] (count : α → ℕ) (ε : ℝ) : ℝ :=
  (∑ x : α, (count x : ℝ)) + (Fintype.card α : ℝ) * ε

/-- Laplace-smoothed counts as a strictly positive measure. -/
noncomputable def regularizedPositiveMeasure
  {α : Type*} [Fintype α] [Nonempty α]
  (count : α → ℕ) (ε : ℝ) (hε : 0 < ε) : PositiveMeasure α ℝ :=
  ⟨fun x => (count x : ℝ) + ε, by
    intro x
    exact add_pos_of_nonneg_of_pos (Nat.cast_nonneg _) hε⟩

@[simp] lemma regularizedPositiveMeasure_apply
  {α : Type*} [Fintype α] [Nonempty α]
  (count : α → ℕ) (ε : ℝ) (hε : 0 < ε) (x : α) :
  regularizedPositiveMeasure count ε hε x = (count x : ℝ) + ε := rfl

/-- `regTotalCount` is exactly the canonical partition `Z` of the smoothed positive measure. -/
lemma regTotalCount_eq_Z_regularizedPositiveMeasure
  {α : Type*} [Fintype α] [Nonempty α]
  (count : α → ℕ) (ε : ℝ) (hε : 0 < ε) :
  regTotalCount count ε = PositiveMeasure.Z (regularizedPositiveMeasure count ε hε) := by
  unfold regTotalCount PositiveMeasure.Z regularizedPositiveMeasure
  rw [Finset.sum_add_distrib, Finset.sum_const]
  simp [nsmul_eq_mul, mul_comm]

/--
Prove the partition function is strictly positive.  (Completing the
missing proof from the previous snippet.)  -/
lemma regTotalCount_pos {α : Type*} [Fintype α] [Nonempty α] (count : α → ℕ) (ε : ℝ) (hε : 0 < ε) :
  0 < regTotalCount count ε := by
  have hZpos : 0 < PositiveMeasure.Z (regularizedPositiveMeasure count ε hε) :=
    PositiveMeasure.Z_pos (regularizedPositiveMeasure count ε hε)
  simpa [regTotalCount_eq_Z_regularizedPositiveMeasure count ε hε] using hZpos

/--
The regularized empirical PMF.  No state is ever completely annihilated.
-/
noncomputable def regularizedPMF {α : Type*} [Fintype α] [Nonempty α] (count : α → ℕ) (ε : ℝ) (hε : 0 < ε) : α → ℝ :=
  PositiveMeasure.toProbabilityFun (regularizedPositiveMeasure count ε hε)

@[simp] lemma regularizedPMF_eq
  {α : Type*} [Fintype α] [Nonempty α]
  (count : α → ℕ) (ε : ℝ) (hε : 0 < ε) (x : α) :
  regularizedPMF count ε hε x = ((count x : ℝ) + ε) / regTotalCount count ε := by
  unfold regularizedPMF PositiveMeasure.toProbabilityFun
  rw [← regTotalCount_eq_Z_regularizedPositiveMeasure count ε hε]
  simp [regularizedPositiveMeasure]

/--
Prove the regularized PMF is strictly positive for EVERY state.  -/
lemma regularizedPMF_strictly_pos
    {α : Type*} [Fintype α] [Nonempty α]
    (count : α → ℕ) (ε : ℝ) (hε : 0 < ε) (x : α) :
  0 < regularizedPMF count ε hε x := by
  unfold regularizedPMF
  exact PositiveMeasure.toProbabilityFun_pos (regularizedPositiveMeasure count ε hε) x

/-!
### Kullback–Leibler divergence utilities
These definitions are intentionally minimal; we only need the divergence
on arbitrary functions so that we can plug in our regularized PMFs.
-/
/-- Standard discrete Kullback–Leibler divergence: `∑ P(x) * log (P(x) / Q(x))`. -/
noncomputable def klDivergence {α : Type*} [Fintype α] (P Q : α → ℝ) : ℝ :=
  ∑ x : α, P x * Real.log (P x / Q x)

/-- The KL divergence evaluated specifically on our regularized PMFs. -/
noncomputable def regularizedKL
    {α : Type*} [Fintype α] [Nonempty α]
    (countP countQ : α → ℕ)
    (ε : ℝ) (hε : 0 < ε) : ℝ :=
  klDivergence (regularizedPMF (α := α) countP ε hε) (regularizedPMF (α := α) countQ ε hε)

/-- Canonical positive-cone generalized KL on the regularized measures. -/
noncomputable def regularizedGeneralizedKL
    {α : Type*} [Fintype α] [Nonempty α]
    (countP countQ : α → ℕ) (ε : ℝ) (hε : 0 < ε) : ℝ :=
  PositiveMeasure.generalizedKL
    (regularizedPositiveMeasure countP ε hε)
    (regularizedPositiveMeasure countQ ε hε)

/-- Nonnegativity inherited from the canonical positive-cone generalized KL theorem. -/
theorem regularizedGeneralizedKL_nonneg
  {α : Type*} [Fintype α] [Nonempty α]
  (countP countQ : α → ℕ) (ε : ℝ) (hε : 0 < ε) :
  0 ≤ regularizedGeneralizedKL countP countQ ε hε := by
  unfold regularizedGeneralizedKL
  exact PositiveMeasure.generalizedKL_nonneg
    (μ := regularizedPositiveMeasure countP ε hε)
    (ν := regularizedPositiveMeasure countQ ε hε)

/--
THE CORE THEOREM:
Because of the “vacuum energy” `ε > 0`, the argument to the logarithm is
mathematically guaranteed to be STRICTLY POSITIVE.  We completely bypass
any `log 0` singularity.  Absolute continuity is guaranteed.
-/
theorem regularized_kl_is_safe
    {α : Type*} [Fintype α] [Nonempty α]
    (countP countQ : α → ℕ) (ε : ℝ) (hε : 0 < ε) (x : α) :
  0 < (regularizedPMF countP ε hε x) / (regularizedPMF countQ ε hε x) := by
  -- A division of two strictly positive numbers is strictly positive.
  apply div_pos
  · exact regularizedPMF_strictly_pos countP ε hε x
  · exact regularizedPMF_strictly_pos countQ ε hε x


/-- The regularized PMF is a genuine probability vector (sums to one). -/
lemma sum_regularizedPMF_eq_one
  {α : Type*} [Fintype α] [Nonempty α]
  (count : α → ℕ) (ε : ℝ) (hε : 0 < ε) :
  ∑ x : α, regularizedPMF count ε hε x = 1 := by
  have hZpos : 0 < regTotalCount count ε := regTotalCount_pos count ε hε
  have hnum : ∑ x : α, ((count x : ℝ) + ε) = regTotalCount count ε := by
    unfold regTotalCount
    rw [Finset.sum_add_distrib, Finset.sum_const]
    simp [nsmul_eq_mul, mul_comm]
  calc
    ∑ x : α, regularizedPMF count ε hε x
        = (∑ x : α, ((count x : ℝ) + ε)) / regTotalCount count ε := by
            simp [regularizedPMF_eq, Finset.sum_div]
    _ = 1 := by
          rw [hnum]
          exact div_self (ne_of_gt hZpos)

end StatisticalMechanics
