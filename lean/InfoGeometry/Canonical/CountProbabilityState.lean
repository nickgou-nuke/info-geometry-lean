import InfoGeometry.KL.Finite

namespace InfoGeometry.Canonical.CountSubstrateBridge

open InfoGeometry
open InfoGeometry.KL

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

/-- Pointwise specification of the empirical probability state. -/
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

/-- Packaging witness for the empirical probability state. -/
private theorem exists_empiricalProbabilityState {α : Type*} [Fintype α]
    (N : CountSubstrate α) (hN : CountSubstrateNontrivial N) :
    ∃ P : ProbabilityDist α, ∀ x : α, (P x).toReal = empirical_distribution N x :=
  ⟨empiricalProbabilityState N hN, empiricalProbabilityState_spec N hN⟩

end CountsToProbability

end InfoGeometry.Canonical.CountSubstrateBridge
