import InfoGeometry.KL.Finite

namespace InfoGeometry.Canonical.CountSubstrateBridge

open InfoGeometry
open InfoGeometry.KL

section CountsToProbability

variable {α : Type*} [Fintype α]

/-- Count substrate: empirical event counts. -/
abbrev CountSubstrate (α : Type*) := EmpiricalCounts α

/-- Canonical empirical probability state induced by counts. -/
noncomputable def empiricalProbabilityState {α : Type*} [Fintype α]
    (N : CountSubstrate α) (hN : empirical_nontrivial N) :
    ProbabilityDist α :=
  empirical_fin_prob N hN

/-- Pointwise specification of the empirical probability state. -/
theorem empiricalProbabilityState_spec {α : Type*} [Fintype α]
    (N : CountSubstrate α) (hN : empirical_nontrivial N) :
    ∀ x : α, (empiricalProbabilityState N hN x).toReal = empirical_distribution N x := by
  intro x
  have htotal_pos : 0 < ∑ y, (N y : ℝ) := by
    exact_mod_cast hN
  have hratio_nonneg : 0 ≤ (N x : ℝ) / (∑ y, (N y : ℝ)) := by
    exact div_nonneg (Nat.cast_nonneg _) htotal_pos.le
  simp [empiricalProbabilityState, empirical_fin_prob, empirical_distribution,
    htotal_pos.ne', hratio_nonneg]

/-- The empirical distribution induced by nontrivial counts is pointwise nonnegative. -/
theorem empirical_distribution_nonneg
    (N : CountSubstrate α) (hN : empirical_nontrivial N) (x : α) :
    0 ≤ empirical_distribution N x := by
  have htotal_pos : 0 < ∑ y, (N y : ℝ) := by
    exact_mod_cast hN
  have htotal_ne : (∑ y, (N y : ℝ)) ≠ 0 := htotal_pos.ne'
  simp [empirical_distribution, htotal_ne, div_nonneg (Nat.cast_nonneg _) htotal_pos.le]

/-- The empirical distribution induced by nontrivial counts has total mass one. -/
theorem empirical_distribution_sum_eq_one
    (N : CountSubstrate α) (hN : empirical_nontrivial N) :
    ∑ x : α, empirical_distribution N x = 1 := by
  have htotal_pos : 0 < ∑ y, (N y : ℝ) := by
    exact_mod_cast hN
  have htotal_ne : (∑ y, (N y : ℝ)) ≠ 0 := htotal_pos.ne'
  simp only [empirical_distribution, htotal_ne, ↓reduceIte]
  rw [← Finset.sum_div]
  exact div_self htotal_ne

/-- Packaging property for the empirical probability state. -/
private theorem exists_empiricalProbabilityState {α : Type*} [Fintype α]
    (N : CountSubstrate α) (hN : empirical_nontrivial N) :
    ∃ P : ProbabilityDist α, ∀ x : α, (P x).toReal = empirical_distribution N x :=
  ⟨empiricalProbabilityState N hN, empiricalProbabilityState_spec N hN⟩

end CountsToProbability

end InfoGeometry.Canonical.CountSubstrateBridge
