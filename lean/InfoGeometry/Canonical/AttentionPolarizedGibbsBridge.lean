import InfoGeometry.Canonical.AttentionPolarizedSplit
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.GrandCanonical.Core
import InfoGeometry.Meta.Architecture

/-!
# Polarized Split Attention as a Gibbs State

This module identifies positive-sheet split attention with the finite Gibbs
distribution of the induced polarized split score.
-/

namespace InfoGeometry.Canonical.Attention

open InfoGeometry.Canonical.Attention
open InfoGeometry.Convex.LogSumExp
open InfoGeometry.GrandCanonical
open scoped BigOperators

section Weights

variable {E V : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {n : ℕ}

/-- Grand-canonical parameters induced by the positive-sheet split score. -/
noncomputable def polarizedPlusParams
    (q : E) (ctx : ContextWindow n E V) :
    GrandCanonicalParams (Fin n) where
  energy := fun i => -polarizedPlusScore (E := E) q (ctx.keys i)

-- theorem-class: bridge
/-- The polarized grand-canonical energy is the negative positive-sheet split score. -/
@[simp] theorem polarizedPlusParams_energy
    (q : E) (ctx : ContextWindow n E V) (i : Fin n) :
    (polarizedPlusParams (E := E) (V := V) q ctx).energy i
      = -polarizedPlusScore (E := E) q (ctx.keys i) := rfl

-- theorem-class: bridge
/-- The polarized split energy is the key-regularized Euclidean energy induced by the split score. -/
theorem polarizedPlusParams_energy_eq_neg_dot_plus_half_norms
    (q : E) (ctx : ContextWindow n E V) (i : Fin n) :
    (polarizedPlusParams (E := E) (V := V) q ctx).energy i
      = -(inner ℝ q (ctx.keys i)
          - (1 / 2 : ℝ) * inner ℝ q q
          - (1 / 2 : ℝ) * inner ℝ (ctx.keys i) (ctx.keys i)) := by
  simp [polarizedPlusParams, polarizedPlusScore_eq_dot_minus_half_norms]

-- theorem-class: bridge
/-- Positive-sheet split attention is the softmax of its induced split score logits. -/
private theorem polarizedPlusAttentionWeights_eq_softmax_score
    [Fact (0 < n)] [AddCommMonoid V] [Module ℝ V]
    (q : E) (ctx : ContextWindow n E V) (β : ℝ) :
    polarizedPlusAttentionWeights (E := E) (V := V) q ctx β
      = softmax (n := Fin n) (fun i => β * polarizedPlusScore (E := E) q (ctx.keys i)) := by
  letI : Nonempty (Fin n) := ⟨⟨0, Fact.out⟩⟩
  rfl

-- theorem-class: bridge
/--
The grand-canonical partition of the polarized split energy is exactly the
normalizing sum of exponentiated polarized attention logits.
-/
@[simp] theorem partition_polarizedPlusParams_eq_logitSum
    (q : E) (ctx : ContextWindow n E V) (β : ℝ) :
    partition (polarizedPlusParams (E := E) (V := V) q ctx) β
      = ∑ i : Fin n, Real.exp (β * polarizedPlusScore (E := E) q (ctx.keys i)) := by
  unfold partition polarizedPlusParams
  refine Finset.sum_congr rfl ?_
  intro i hi
  congr 1
  ring_nf

-- theorem-class: bridge
/--
Positive-sheet split attention weights are exactly the Gibbs weights of the
polarized split energy observable.
-/
@[rep_depth thermo, simp]
theorem gibbsWeight_polarizedPlusParams_eq_polarizedPlusAttentionWeights
    [Fact (0 < n)] [AddCommMonoid V] [Module ℝ V]
    (q : E) (ctx : ContextWindow n E V) (β : ℝ) (i : Fin n) :
    gibbsWeight (polarizedPlusParams (E := E) (V := V) q ctx) β i
      = polarizedPlusAttentionWeights (E := E) (V := V) q ctx β i := by
  letI : Nonempty (Fin n) := ⟨⟨0, Fact.out⟩⟩
  rw [polarizedPlusAttentionWeights_eq_softmax_score (E := E) (V := V) q ctx β]
  unfold gibbsWeight softmax sumExp partition polarizedPlusParams
  congr 1
  · ring_nf
  · refine Finset.sum_congr rfl ?_
    intro j hj
    congr 1
    ring_nf


-- theorem-class: bridge
/-- Under constant key norm, the polarized Gibbs weights reduce to Euclidean Gibbs weights. -/
theorem polarizedPlusAttentionWeights_eq_euclideanGibbsWeights_of_constantKeyNorm
    [Fact (0 < n)] [AddCommMonoid V] [Module ℝ V]
    (q : E) (ctx : ContextWindow n E V) (β κ : ℝ)
    (hκ : ∀ i, ‖ctx.keys i‖ ^ 2 = κ) :
    polarizedPlusAttentionWeights (E := E) (V := V) q ctx β
      = fun i => gibbsWeight (euclideanAttentionParams q ctx) β i := by
  funext i
  rw [polarizedPlusAttentionWeights_eq_euclideanAttentionWeights_of_constantKeyNorm
    (E := E) (V := V) (q := q) (ctx := ctx) (β := β) (κ := κ) hκ]
  rfl

end Weights

section Head

variable {E V : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable [AddCommMonoid V] [Module ℝ V]
variable {n : ℕ}

-- theorem-class: bridge
/--
The positive-sheet split attention head is the Gibbs expectation of the values
under the polarized split grand-canonical ensemble.
-/
theorem polarizedPlusAttentionHead_eq_gibbsExpectation
    [Fact (0 < n)]
    (q : E) (ctx : ContextWindow n E V) (β : ℝ) :
    polarizedPlusAttentionHead (E := E) (V := V) q ctx β
      = ∑ i, gibbsWeight (polarizedPlusParams (E := E) (V := V) q ctx) β i • ctx.values i := by
  letI : Nonempty (Fin n) := ⟨⟨0, Fact.out⟩⟩
  unfold polarizedPlusAttentionHead
  simp [gibbsWeight_polarizedPlusParams_eq_polarizedPlusAttentionWeights (E := E) (V := V)
    (q := q) (ctx := ctx) (β := β)]

end Head

end InfoGeometry.Canonical.Attention
