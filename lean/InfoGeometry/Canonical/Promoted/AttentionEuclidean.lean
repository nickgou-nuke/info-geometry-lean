import Mathlib.Analysis.InnerProductSpace.Basic
import InfoGeometry.Canonical.Promoted.Attention

/-!
# Euclidean Attention (Standard Dot-Product Specialization)

This module instantiates the thermodynamic Attention mechanism
using the standard Euclidean dot product.
-/

namespace InfoGeometry.Research.Attention

open scoped BigOperators

variable {S V : Type*}
variable [NormedAddCommGroup S] [InnerProductSpace ℝ S]
variable [AddCommMonoid V] [Module ℝ V]

/-- The standard Euclidean matching form (inner product as a bilinear map). -/
noncomputable def euclideanMatchForm : S →ₗ[ℝ] S →ₗ[ℝ] ℝ :=
{ toFun := fun q =>
    { toFun := fun k => inner ℝ q k
      map_add' := fun k₁ k₂ => inner_add_right q k₁ k₂
      map_smul' := fun a k => by simp [inner_smul_right, smul_eq_mul] }
  map_add' := fun q₁ q₂ => by
    apply LinearMap.ext
    intro k
    simp [inner_add_left]
  map_smul' := fun a q => by
    apply LinearMap.ext
    intro k
    simp [inner_smul_left, smul_eq_mul, RingHom.id_apply] }

variable {n : ℕ} [Fact (0 < n)]

/-- Standard Attention Params. -/
noncomputable abbrev euclideanAttentionParams
    (q : S)
    (ctx : ContextWindow n S V) :
    InfoGeometry.GrandCanonical.GrandCanonicalParams (Fin n) :=
  attentionParams q ctx euclideanMatchForm

/-- Standard Attention Weights (Softmax). -/
noncomputable abbrev euclideanAttentionWeights
    (q : S)
    (ctx : ContextWindow n S V)
    (β : ℝ) (i : Fin n) : ℝ :=
  attentionWeights q ctx euclideanMatchForm β i

/-- Standard Attention Head output. -/
noncomputable abbrev euclideanAttentionHead
    (q : S)
    (ctx : ContextWindow n S V)
    (β : ℝ) : V :=
  attentionHead q ctx euclideanMatchForm β

omit [AddCommMonoid V] [Module ℝ V] in
/-- Theorem: Standard Attention is rigorously normalized. -/
lemma euclideanAttentionWeights_sum_one
    (q : S)
    (ctx : ContextWindow n S V)
    (β : ℝ) :
    ∑ i, euclideanAttentionWeights q ctx β i = 1 := by
  haveI : Nonempty (Fin n) := ⟨⟨0, Fact.out⟩⟩
  simpa [euclideanAttentionWeights] using 
    attentionWeights_sum_one q ctx euclideanMatchForm β

end InfoGeometry.Research.Attention
