import proofs.NonIsoConf3DeRhamCooperad
import proofs.NonIsoConf3RankDecision

/-!
# Pairwise non-isotropic three-point quadric configurations

This is a compact entry point for the problem

`F_Q(ℂ^D,3) = {(x₁,x₂,x₃) : q(xᵢ-xⱼ) ≠ 0 for i<j}`,

with `D` even.  It packages the already-verified finite Lean spine:

* translation reduction `Config3 D ≃ Reduced3 D`;
* product/Leray candidate rank `32`, corresponding to
  `(1+t)^3(1+t^(D-1))^2`;
* OS-alpha candidate rank `24`;
* arity-three cooperad internal/outer edge bookkeeping.

The analytic identification of the finite candidate with actual de Rham
cohomology remains an explicit `ConcreteDeRhamCooperadData`.
-/

namespace NonIsoConf3PairwiseNonisotropicCohomology

open QuadraticConfiguration3
open NonIsoConf3DeRhamCooperad
open NonIsoConf3RankDecision

/-- The full three-point configuration is equivalent to the translation-reduced
configuration data.  The discarded translation factor is contractible in the
intended geometric interpretation. -/
theorem translation_reduction (D : ℕ) :
    Nonempty (Config3 D ≃ Reduced3 D) :=
  ⟨config3_reduced_equiv D⟩

/-- Product/Leray finite signature: total rank `32`. -/
theorem product_leray_total_rank :
    Fintype.card ProductBasis = 32 :=
  productBasis_card

/-- OS-alpha finite signature: total rank `24`. -/
theorem os_alpha_total_rank :
    Fintype.card OSFluxBasis = 24 :=
  osFluxBasis_card

/-- The finite rank gap between the two candidate presentations. -/
theorem product_leray_vs_os_alpha_gap :
    Fintype.card ProductBasis - Fintype.card OSFluxBasis = 8 :=
  product_vs_os_rank_gap

/-- Every arity-three collision has an internal alpha edge and an internal beta
edge.  This is the finite cooperad bookkeeping used by the de Rham interface. -/
theorem cooperad_internal_alpha_beta :
    (∀ b : BlockDecomp3, ∃ e : Edge3,
      cooperadOnAlpha b e = (TargetFactor.internal, GenKind.alpha)) ∧
    (∀ b : BlockDecomp3, ∃ e : Edge3,
      cooperadOnBeta b e = (TargetFactor.internal, GenKind.beta)) :=
  ⟨cooperad_alpha_has_internal_edge, cooperad_beta_has_internal_edge⟩

/-- Conditional de Rham/cooperad theorem: once the analytic interface identifies
the product/Leray presentation with the actual de Rham model, the computed
rank is `32` and the arity-three cooperad bookkeeping is compatible. -/
theorem pairwise_nonisotropic_derham_product_leray
    {D : ℕ} (S : ConcreteDeRhamCooperadData D)
    (hChoice : S.relationChoice = ModelChoice.productLeray) :
    Nonempty (Config3 D ≃ Reduced3 D) ∧
    Fintype.card ProductBasis = 32 ∧
    (∀ b : BlockDecomp3, ∃ e : Edge3,
      cooperadOnAlpha b e = (TargetFactor.internal, GenKind.alpha)) ∧
    (∀ b : BlockDecomp3, ∃ e : Edge3,
      cooperadOnBeta b e = (TargetFactor.internal, GenKind.beta)) := by
  exact ⟨translation_reduction D,
    product_candidate_rank S hChoice,
    cooperad_alpha_has_internal_edge,
    cooperad_beta_has_internal_edge⟩

/-- Rank-decision bridge: the Dupont/Gysin rank interface selects the rank-32
product/Leray branch over the rank-24 OS-alpha branch. -/
theorem rank_decision_selects_product_leray :
    ¬ tripleDependent expectedCodimData ∧
    Fintype.card ProductBasis = 32 ∧
    Fintype.card OSFluxBasis = 24 ∧
    Fintype.card ProductBasis - Fintype.card OSFluxBasis = 8 :=
  let h := rank32_decision_from_dupont_independence
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2⟩

end NonIsoConf3PairwiseNonisotropicCohomology
