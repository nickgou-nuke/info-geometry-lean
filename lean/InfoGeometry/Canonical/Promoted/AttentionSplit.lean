import Mathlib.Analysis.SpecialFunctions.Log.Basic
import InfoGeometry.Canonical.Promoted.Attention
import InfoGeometry.Clifford.SplitQ11

/-!
# Lorentzian Attention (Split-Signature Interaction)

This module instantiates the thermodynamic Attention mechanism
using the split-signature (1,1) metric from the Clifford algebra module.

By defining the interaction energy via the `splitB11` bilinear form, 
we formalize that the attention head is computing a hyperbolic/Lorentzian
interaction between the Queries and Keys.
-/

namespace InfoGeometry.Research.Attention

open InfoGeometry.Clifford
open scoped BigOperators

variable {n : ℕ} [Fact (0 < n)]
variable {V : Type*}
variable [AddCommMonoid V] [Module ℝ V]

/-- Lorentzian attention parameters induced by the split-signature bilinear form. -/
noncomputable abbrev lorentzianAttentionParams
    (q : ℝ × ℝ)
    (ctx : ContextWindow n (ℝ × ℝ) V) :
    InfoGeometry.GrandCanonical.GrandCanonicalParams (Fin n) :=
  attentionParams q ctx splitB11

/-- Gibbs weights from the split-signature interaction score. -/
noncomputable abbrev lorentzianAttentionWeights
    (q : ℝ × ℝ)
    (ctx : ContextWindow n (ℝ × ℝ) V)
    (β : ℝ) (i : Fin n) : ℝ :=
  attentionWeights q ctx splitB11 β i

/-- Attention output with Lorentzian query-key geometry and arbitrary value space. -/
noncomputable abbrev lorentzianAttentionHead
    (q : ℝ × ℝ)
    (ctx : ContextWindow n (ℝ × ℝ) V)
    (β : ℝ) : V :=
  attentionHead q ctx splitB11 β

omit [AddCommMonoid V] [Module ℝ V] in
/-- Theorem: Lorentzian Attention is rigorously normalized. -/
lemma lorentzianAttentionWeights_sum_one
    (q : ℝ × ℝ)
    (ctx : ContextWindow n (ℝ × ℝ) V)
    (β : ℝ) :
    ∑ i, lorentzianAttentionWeights q ctx β i = 1 := by
  haveI : Nonempty (Fin n) := ⟨⟨0, Fact.out⟩⟩
  simpa [lorentzianAttentionWeights] using
    attentionWeights_sum_one q ctx splitB11 β

end InfoGeometry.Research.Attention
