import InfoGeometry.Canonical.AttentionSplit
import InfoGeometry.Meta.Architecture

open scoped BigOperators

namespace KreinAttentionEnergy

open InfoGeometry.Canonical.Attention
open InfoGeometry.Clifford

variable {V : Type*}
variable [AddCommMonoid V] [Module ℝ V]
variable {n : ℕ} [Fact (0 < n)]

/-- Split-signature (Krein/Lorentzian) interaction energy on the `Q-K` lane. -/
noncomputable def kreinInteractionEnergy (q k : ℝ × ℝ) : ℝ :=
  interactionEnergy q k splitB11

/-- Explicit split-signature form of the interaction energy. -/
@[simp, rep_depth krein]
theorem kreinInteractionEnergy_eq_neg_splitB11
    (q k : ℝ × ℝ) :
    kreinInteractionEnergy q k = -(q.1 * k.1 - q.2 * k.2) := by
  simp [kreinInteractionEnergy, interactionEnergy, splitB11_apply]

/-- Token-local normalized attention weights over a split-signature interaction lane. -/
noncomputable def kreinAttentionWeights
    (q : ℝ × ℝ)
    (ctx : ContextWindow n (ℝ × ℝ) V)
    (β : ℝ) (i : Fin n) : ℝ :=
  attentionWeights q ctx splitB11 β i

/-- The split-signature attention head (Gibbs expectation of values). -/
noncomputable def kreinAttentionHead
    (q : ℝ × ℝ)
    (ctx : ContextWindow n (ℝ × ℝ) V)
    (β : ℝ) : V :=
  attentionHead q ctx splitB11 β

omit [AddCommMonoid V] [Module ℝ V] in
/-- Normalization law on the Krein attention lane (`∑ᵢ wᵢ = 1`). -/
@[rep_depth thermo]
theorem kreinAttentionWeights_sum_one
    (q : ℝ × ℝ)
    (ctx : ContextWindow n (ℝ × ℝ) V)
    (β : ℝ) :
    ∑ i, kreinAttentionWeights (V := V) q ctx β i = 1 := by
  haveI : Nonempty (Fin n) := ⟨⟨0, Fact.out⟩⟩
  simpa [kreinAttentionWeights] using
    (attentionWeights_sum_one (q := q) (ctx := ctx) (matchForm := splitB11) (β := β))

end KreinAttentionEnergy
