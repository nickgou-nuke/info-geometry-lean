import InfoGeometry.Basic

/-!
# Finite KL Divergence

KL divergence for finite probability spaces.
Rebased onto the canonical `FinProb` (PMF) foundation.
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
Delegates to the canonical `kl_div` on the underlying measures.
-/
noncomputable def divergence {α : Type*} [MeasurableSpace α]
    (p q : FinProb α) : ℝ≥0∞ :=
  InfoGeometry.kl_div p.toMeasure q.toMeasure

/-- Non-negativity of finite KL (Gibbs inequality). -/
theorem divergence_nonneg {α : Type*} [MeasurableSpace α]
    (p q : FinProb α) : 0 ≤ divergence p q :=
  zero_le _

end InfoGeometry.KL
