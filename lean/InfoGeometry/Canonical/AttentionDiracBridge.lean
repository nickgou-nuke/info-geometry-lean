import InfoGeometry.Canonical.Attention

/-!
# InfoGeometry.Canonical.AttentionDiracBridge

Conservative bridge between the existing thermodynamic attention API and a
Dirac-labeled bilinear pairing.

This file does **not** claim a canonical identity theorem of the form
"attention is the Dirac operator". It only states the strict transport facts
that are currently justified in the repository:

- choose any bilinear pairing `diracPairing` on query/key spaces,
- instantiate attention with that pairing,
- and, whenever another matching form is definitionally identified with it,
  all induced energies/params/weights/heads are equal.
-/

namespace InfoGeometry.Canonical.AttentionDiracBridge

open InfoGeometry.Canonical.Attention
open scoped BigOperators

section Core

variable {S_plus S_minus V : Type*}
variable [AddCommGroup S_plus] [Module ℝ S_plus]
variable [AddCommGroup S_minus] [Module ℝ S_minus]
variable [AddCommMonoid V] [Module ℝ V]

/-- A Dirac-labeled bilinear pairing used as an attention matching form. -/
abbrev DiracPairing := S_plus →ₗ[ℝ] S_minus →ₗ[ℝ] ℝ

variable {n : ℕ} [Fact (0 < n)]

/-- Attention parameters instantiated by a chosen Dirac pairing. -/
noncomputable abbrev diracAttentionParams
    (q : S_plus)
    (ctx : ContextWindow n S_minus V)
    (diracPairing : DiracPairing (S_plus := S_plus) (S_minus := S_minus)) :
    InfoGeometry.GrandCanonical.GrandCanonicalParams (Fin n) :=
  attentionParams q ctx diracPairing

/-- Attention weights instantiated by a chosen Dirac pairing. -/
noncomputable abbrev diracAttentionWeights
    (q : S_plus)
    (ctx : ContextWindow n S_minus V)
    (diracPairing : DiracPairing (S_plus := S_plus) (S_minus := S_minus))
    (β : ℝ) (i : Fin n) : ℝ :=
  attentionWeights q ctx diracPairing β i

/-- Attention head instantiated by a chosen Dirac pairing. -/
noncomputable abbrev diracAttentionHead
    (q : S_plus)
    (ctx : ContextWindow n S_minus V)
    (diracPairing : DiracPairing (S_plus := S_plus) (S_minus := S_minus))
    (β : ℝ) : V :=
  attentionHead q ctx diracPairing β

/-- Interaction energy is invariant under explicit identification of matching forms. -/
lemma interactionEnergy_eq_of_matchForm_eq_diracPairing
    (q : S_plus)
    (k : S_minus)
    (matchForm diracPairing : DiracPairing (S_plus := S_plus) (S_minus := S_minus))
    (hMatch : matchForm = diracPairing) :
    interactionEnergy q k matchForm = interactionEnergy q k diracPairing := by
  cases hMatch
  rfl

-- Attention parameters are invariant under explicit identification of matching forms.
omit [AddCommMonoid V] [Module ℝ V] [Fact (0 < n)] in
lemma attentionParams_eq_of_matchForm_eq_diracPairing
    (q : S_plus)
    (ctx : ContextWindow n S_minus V)
    (matchForm diracPairing : DiracPairing (S_plus := S_plus) (S_minus := S_minus))
    (hMatch : matchForm = diracPairing) :
    attentionParams q ctx matchForm = attentionParams q ctx diracPairing := by
  cases hMatch
  rfl

-- Attention weights are invariant under explicit identification of matching forms.
omit [AddCommMonoid V] [Module ℝ V] [Fact (0 < n)] in
lemma attentionWeights_eq_of_matchForm_eq_diracPairing
    (q : S_plus)
    (ctx : ContextWindow n S_minus V)
    (matchForm diracPairing : DiracPairing (S_plus := S_plus) (S_minus := S_minus))
    (β : ℝ) (i : Fin n)
    (hMatch : matchForm = diracPairing) :
    attentionWeights q ctx matchForm β i = attentionWeights q ctx diracPairing β i := by
  cases hMatch
  rfl

-- Attention-head output is invariant under explicit identification of matching forms.
omit [Fact (0 < n)] in
lemma attentionHead_eq_of_matchForm_eq_diracPairing
    (q : S_plus)
    (ctx : ContextWindow n S_minus V)
    (matchForm diracPairing : DiracPairing (S_plus := S_plus) (S_minus := S_minus))
    (β : ℝ)
    (hMatch : matchForm = diracPairing) :
    attentionHead q ctx matchForm β = attentionHead q ctx diracPairing β := by
  cases hMatch
  rfl

omit [AddCommMonoid V] [Module ℝ V] in
/-- Dirac-labeled attention weights are normalized (partition of unity). -/
lemma diracAttentionWeights_sum_one
    (q : S_plus)
    (ctx : ContextWindow n S_minus V)
    (diracPairing : DiracPairing (S_plus := S_plus) (S_minus := S_minus))
    (β : ℝ) :
    ∑ i, diracAttentionWeights q ctx diracPairing β i = 1 := by
  haveI : Nonempty (Fin n) := ⟨⟨0, Fact.out⟩⟩
  simpa [diracAttentionWeights] using attentionWeights_sum_one q ctx diracPairing β

end Core

end InfoGeometry.Canonical.AttentionDiracBridge
