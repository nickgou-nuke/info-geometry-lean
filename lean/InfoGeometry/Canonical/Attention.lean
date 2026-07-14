import Architect
import InfoGeometry.GrandCanonical.Core
import Mathlib.Algebra.Module.Basic

/-!
# Spinorial Thermodynamics of Transformer Attention

This module formalizes the Scaled Dot-Product Attention mechanism as a
thermodynamic process over a triality of vector spaces.

- `S⁺` (Queries) and `S⁻` (Keys) interact via a bilinear form (the Hamiltonian).
- `V` (Values) is the semantic vector space.
- Softmax is formalized as the Gibbs distribution of the Grand Canonical ensemble.
- The scaling factor `1/√d` acts as the inverse temperature `β`.
-/

namespace Attention

open InfoGeometry.GrandCanonical
open scoped BigOperators

variable {S_plus S_minus V : Type*}
variable [AddCommGroup S_plus] [Module ℝ S_plus]
variable [AddCommGroup S_minus] [Module ℝ S_minus]
variable [AddCommMonoid V] [Module ℝ V]

/-- The interaction energy between a Query (S⁺) and a Key (S⁻).
In standard attention, S⁺ and S⁻ are isomorphic and this is the dot product.
We represent the matching as an abstract bilinear form, yielding negative energy. -/
def interactionEnergy (q : S_plus) (k : S_minus) (matchForm : S_plus →ₗ[ℝ] S_minus →ₗ[ℝ] ℝ) : ℝ :=
  - (matchForm q k)

/-- A sequence of Keys and Values of length `n` (The Context Window). -/
structure ContextWindow (n : ℕ) (S_minus V : Type*) where
  keys : Fin n → S_minus
  values : Fin n → V

variable {n : ℕ} [Fact (0 < n)]

/-- The Attention Hamiltonian for a specific Query over the Context Window.
The energy of each token is the negative matching score. -/
noncomputable def attentionParams
    (q : S_plus)
    (ctx : ContextWindow n S_minus V)
    (matchForm : S_plus →ₗ[ℝ] S_minus →ₗ[ℝ] ℝ) :
    GrandCanonicalParams (Fin n) where
  energy := fun i => interactionEnergy q (ctx.keys i) matchForm

/-- The Attention Weights are exactly the Gibbs distribution.
The inverse temperature β corresponds to `1 / √d`. -/
noncomputable def attentionWeights
    (q : S_plus)
    (ctx : ContextWindow n S_minus V)
    (matchForm : S_plus →ₗ[ℝ] S_minus →ₗ[ℝ] ℝ)
    (β : ℝ) (i : Fin n) : ℝ :=
  gibbsWeight (attentionParams q ctx matchForm) β i

/-- The output of the Attention Head is the Gibbs expectation over the Value space `V`. -/
@[blueprint "def:attention-head-output"]
noncomputable def attentionHead
    (q : S_plus)
    (ctx : ContextWindow n S_minus V)
    (matchForm : S_plus →ₗ[ℝ] S_minus →ₗ[ℝ] ℝ)
    (β : ℝ) : V :=
  ∑ i, attentionWeights q ctx matchForm β i • ctx.values i

omit [AddCommMonoid V] [Module ℝ V] in
/-- Theorem: Attention weights sum to 1 (Conservation of Information / Partition of Unity). 
This proves that Attention is a rigorously normalized thermodynamic state. -/
@[blueprint "thm:attention-weights-normalization"]
lemma attentionWeights_sum_one
    (q : S_plus)
    (ctx : ContextWindow n S_minus V)
    (matchForm : S_plus →ₗ[ℝ] S_minus →ₗ[ℝ] ℝ)
    (β : ℝ) :
    ∑ i, attentionWeights q ctx matchForm β i = 1 := by
  haveI : Nonempty (Fin n) := ⟨⟨0, Fact.out⟩⟩
  simpa [attentionWeights] using
    gibbsWeight_sum_one (attentionParams q ctx matchForm) β

omit [AddCommMonoid V] [Module ℝ V] in
/-- Attention weights are pointwise nonnegative. -/
lemma attentionWeights_nonneg
    (q : S_plus)
    (ctx : ContextWindow n S_minus V)
    (matchForm : S_plus →ₗ[ℝ] S_minus →ₗ[ℝ] ℝ)
    (β : ℝ) (i : Fin n) :
    0 ≤ attentionWeights q ctx matchForm β i := by
  haveI : Nonempty (Fin n) := ⟨⟨0, Fact.out⟩⟩
  simpa [attentionWeights] using
    gibbsWeight_nonneg (attentionParams q ctx matchForm) β i

omit [AddCommMonoid V] [Module ℝ V] in
/-- Attention weights are pointwise bounded by one. -/
lemma attentionWeights_le_one
    (q : S_plus)
    (ctx : ContextWindow n S_minus V)
    (matchForm : S_plus →ₗ[ℝ] S_minus →ₗ[ℝ] ℝ)
    (β : ℝ) (i : Fin n) :
    attentionWeights q ctx matchForm β i ≤ 1 := by
  haveI : Nonempty (Fin n) := ⟨⟨0, Fact.out⟩⟩
  simpa [attentionWeights] using
    gibbsWeight_le_one (attentionParams q ctx matchForm) β i

end Attention
