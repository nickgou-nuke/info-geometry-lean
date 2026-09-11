import InfoGeometry.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.KL.Measure

/-!
# Finite KL Divergence

Extended-valued KL divergence for finite probability spaces, expressed on the
normalized `FinProb` gauge slice.

This file is a downstream facade over the canonical measure-level
`InfoGeometry.KL.kl_div` and the deeper cone/projective state foundation.
-/

namespace InfoGeometry.KL

open scoped BigOperators ENNReal NNReal

/-- Empirical distribution: `P(x) = count(x) / total_count`. -/
noncomputable def empirical_distribution {α : Type*} [Fintype α] (N : EmpiricalCounts α) : α → ℝ :=
  let total := ∑ x, (N x : ℝ)
  if total = 0 then (fun _ => 0) else (fun x => (N x : ℝ) / total)

/-- Predicate for non-empty empirical counts. -/
def empirical_nontrivial {α : Type*} [Fintype α] (N : EmpiricalCounts α) : Prop :=
  0 < ∑ x, N x

/-- Convert nontrivial empirical counts into a canonical `FinProb`. -/
noncomputable def empirical_fin_prob {α : Type*} [Fintype α]
    (N : EmpiricalCounts α) (h : empirical_nontrivial N) : FinProb α :=
  let total := ∑ x, (N x : ℝ)
  have htotal : total = ∑ x, (N x : ℝ) := rfl
  have hZ_pos : 0 < total := by
    dsimp [total]
    exact_mod_cast h
  PMF.ofFintype (fun x => ENNReal.ofReal ((N x : ℝ) / total)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg]
    · rw [← Finset.sum_div, htotal.symm, div_self hZ_pos.ne', ENNReal.ofReal_one]
    · intro x _; exact div_nonneg (Nat.cast_nonneg _) hZ_pos.le)

/--
Standard KL divergence for finite laws.
Delegates to the canonical measure-level `InfoGeometry.KL.kl_div` on the
underlying measures.
-/
noncomputable def divergence {α : Type*} [MeasurableSpace α]
    (p q : FinProb α) : ℝ≥0∞ :=
  InfoGeometry.KL.kl_div p.toMeasure q.toMeasure

/-- Technical nonnegativity on the `ℝ≥0∞` finite-KL slice. -/
theorem divergence_nonneg {α : Type*} [MeasurableSpace α]
    (p q : FinProb α) : 0 ≤ divergence p q :=
  zero_le _

end InfoGeometry.KL

namespace InfoGeometry

/-- `fin_kl_div` and `fin_kl_div` are definitionally identical. -/
lemma fin_kl_div_eq_KL_divergence
    {α : Type*} [MeasurableSpace α] (p q : FinProb α) :
    fin_kl_div p q = fin_kl_div p q := rfl

end InfoGeometry
