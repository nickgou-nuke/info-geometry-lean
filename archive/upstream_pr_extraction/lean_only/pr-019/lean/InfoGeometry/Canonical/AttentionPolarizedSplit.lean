import InfoGeometry.Canonical.AttentionEuclidean
import InfoGeometry.Convex.LogSumExp
import InfoGeometry.Krein.PolarizedSector
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic.Ring
import InfoGeometry.Meta.Architecture

/-!
# Polarized Split Attention

Positive-sheet specialization of split/Krein attention. The score is the negative
restricted split divergence on the `+1` spectral sheet, transported back to the
carrier `E`. The resulting softmax weights reduce first to a key-regularized
Euclidean softmax and, under constant key norm, to ordinary Euclidean attention.
-/

namespace InfoGeometry.Canonical.Attention

open InfoGeometry.Convex.LogSumExp
open InfoGeometry.Krein.PolarizedSector
open InfoGeometry.Krein.SplitQuadraticSheets
open scoped BigOperators

variable {E V : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable [AddCommMonoid V] [Module ℝ V]
variable {n : ℕ} [Fact (0 < n)]

local instance finNonempty : Nonempty (Fin n) := ⟨⟨0, Fact.out⟩⟩

/-- Positive-sheet split attention score, transported back to the carrier `E`. -/
noncomputable def polarizedPlusScore (q k : E) : ℝ :=
  -polarizedDivergence (E := E) (plusPoint (E := E) q) (plusPoint (E := E) k)

private noncomputable def polarizedPlusLogits
    (q : E) (ctx : ContextWindow n E V) (β : ℝ) : Fin n → ℝ :=
  fun i => β * polarizedPlusScore (E := E) q (ctx.keys i)

private noncomputable def keyRegularizedDotLogits
    (q : E) (ctx : ContextWindow n E V) (β : ℝ) : Fin n → ℝ :=
  fun i => β * (inner ℝ q (ctx.keys i)
    - (1 / 2 : ℝ) * inner ℝ (ctx.keys i) (ctx.keys i))

private noncomputable def dotProductLogits
    (q : E) (ctx : ContextWindow n E V) (β : ℝ) : Fin n → ℝ :=
  fun i => β * inner ℝ q (ctx.keys i)

private noncomputable def dotProductSoftmaxWeights
    (q : E) (ctx : ContextWindow n E V) (β : ℝ) : Fin n → ℝ :=
  softmax (n := Fin n) (dotProductLogits (E := E) (V := V) q ctx β)

/-- Positive-sheet split attention weights. -/
@[rep_depth thermo]
noncomputable def polarizedPlusAttentionWeights
    (q : E) (ctx : ContextWindow n E V) (β : ℝ) : Fin n → ℝ :=
  softmax (n := Fin n) (polarizedPlusLogits (E := E) (V := V) q ctx β)

/-- Positive-sheet split attention head. -/
noncomputable def polarizedPlusAttentionHead
    (q : E) (ctx : ContextWindow n E V) (β : ℝ) : V :=
  ∑ i, polarizedPlusAttentionWeights (E := E) (V := V) q ctx β i • ctx.values i

-- theorem-class: bridge
/-- The positive-sheet split score decomposes into dot product minus quadratic penalties. -/
theorem polarizedPlusScore_eq_dot_minus_half_norms (q k : E) :
    polarizedPlusScore (E := E) q k
      = inner ℝ q k - (1 / 2 : ℝ) * inner ℝ q q - (1 / 2 : ℝ) * inner ℝ k k := by
  simpa [polarizedPlusScore] using
    (neg_polarizedDivergence_eq_plusSheet_interaction
      (E := E) (q := plusPoint (E := E) q) (k := plusPoint (E := E) k))

omit [AddCommMonoid V] [Module ℝ V] [Fact (0 < n)] in
private theorem polarizedPlusLogits_eq_keyRegularizedDotLogits_add_uniformShift
    (q : E) (ctx : ContextWindow n E V) (β : ℝ) :
    polarizedPlusLogits (E := E) (V := V) q ctx β
      = keyRegularizedDotLogits (E := E) (V := V) q ctx β
        + (β * (-(1 / 2 : ℝ) * inner ℝ q q)) • uniformShift (n := Fin n) := by
  funext i
  simp [polarizedPlusLogits, keyRegularizedDotLogits, polarizedPlusScore_eq_dot_minus_half_norms,
    uniformShift]
  ring

omit [CompleteSpace E] [AddCommMonoid V] [Module ℝ V] [Fact (0 < n)] in
private theorem keyRegularizedDotLogits_eq_dotProductLogits_add_uniformShift_of_constantKeyNorm
    (q : E) (ctx : ContextWindow n E V) (β κ : ℝ)
    (hκ : ∀ i, ‖ctx.keys i‖ ^ 2 = κ) :
    keyRegularizedDotLogits (E := E) (V := V) q ctx β
      = dotProductLogits (E := E) (V := V) q ctx β
        + (β * (-(1 / 2 : ℝ) * κ)) • uniformShift (n := Fin n) := by
  funext i
  simp [keyRegularizedDotLogits, dotProductLogits, uniformShift, hκ i]
  ring

omit [CompleteSpace E] [AddCommMonoid V] [Module ℝ V] [Fact (0 < n)] in
private theorem dotProductSoftmaxWeights_eq_euclideanAttentionWeights
    (q : E) (ctx : ContextWindow n E V) (β : ℝ) :
    dotProductSoftmaxWeights (E := E) (V := V) q ctx β
      = fun i => euclideanAttentionWeights q ctx β i := by
  funext i
  unfold dotProductSoftmaxWeights InfoGeometry.Convex.LogSumExp.softmax
    InfoGeometry.Convex.LogSumExp.sumExp
  simp [dotProductLogits, euclideanAttentionWeights, attentionWeights,
    attentionParams, interactionEnergy, euclideanMatchForm,
    InfoGeometry.GrandCanonical.gibbsWeight, InfoGeometry.GrandCanonical.partition]

omit [AddCommMonoid V] [Module ℝ V] in
-- theorem-class: closure
/-- Positive-sheet split attention weights are normalized. -/
theorem polarizedPlusAttentionWeights_sum_one
    (q : E) (ctx : ContextWindow n E V) (β : ℝ) :
    ∑ i, polarizedPlusAttentionWeights (E := E) (V := V) q ctx β i = 1 := by
  simpa [polarizedPlusAttentionWeights] using
    (sum_softmax_eq_one (n := Fin n)
      (x := polarizedPlusLogits (E := E) (V := V) q ctx β))

omit [AddCommMonoid V] [Module ℝ V] in
-- theorem-class: bridge
/--
The positive-sheet split softmax weights differ from Euclidean dot-product logits
only by a query-dependent uniform shift, leaving a key-regularized softmax law.
-/
theorem polarizedPlusAttentionWeights_eq_keyRegularizedDotSoftmax
    (q : E) (ctx : ContextWindow n E V) (β : ℝ) :
    polarizedPlusAttentionWeights (E := E) (V := V) q ctx β
      = softmax (n := Fin n)
          (fun i => β * (inner ℝ q (ctx.keys i)
            - (1 / 2 : ℝ) * inner ℝ (ctx.keys i) (ctx.keys i))) := by
  unfold polarizedPlusAttentionWeights
  rw [polarizedPlusLogits_eq_keyRegularizedDotLogits_add_uniformShift (E := E) (V := V) q ctx β]
  change softmax (n := Fin n)
      (keyRegularizedDotLogits (E := E) (V := V) q ctx β
        + (β * (-(1 / 2 : ℝ) * inner ℝ q q)) • uniformShift (n := Fin n))
      = softmax (n := Fin n) (keyRegularizedDotLogits (E := E) (V := V) q ctx β)
  exact softmax_add_uniformShift (n := Fin n)
    (x := keyRegularizedDotLogits (E := E) (V := V) q ctx β)
    (c := β * (-(1 / 2 : ℝ) * inner ℝ q q))

omit [AddCommMonoid V] [Module ℝ V] in
-- theorem-class: bridge
/--
If all keys have the same squared norm, positive-sheet split attention reduces
exactly to the existing Euclidean attention weights.
-/
theorem polarizedPlusAttentionWeights_eq_euclideanAttentionWeights_of_constantKeyNorm
    (q : E) (ctx : ContextWindow n E V) (β κ : ℝ)
    (hκ : ∀ i, ‖ctx.keys i‖ ^ 2 = κ) :
    polarizedPlusAttentionWeights (E := E) (V := V) q ctx β
      = fun i => euclideanAttentionWeights q ctx β i := by
  calc
    polarizedPlusAttentionWeights (E := E) (V := V) q ctx β
        = softmax (n := Fin n)
            (fun i => β * (inner ℝ q (ctx.keys i)
              - (1 / 2 : ℝ) * inner ℝ (ctx.keys i) (ctx.keys i))) := by
            exact polarizedPlusAttentionWeights_eq_keyRegularizedDotSoftmax
              (E := E) (V := V) q ctx β
    _ = softmax (n := Fin n) (dotProductLogits (E := E) (V := V) q ctx β) := by
          change softmax (n := Fin n) (keyRegularizedDotLogits (E := E) (V := V) q ctx β)
            = softmax (n := Fin n) (dotProductLogits (E := E) (V := V) q ctx β)
          rw [keyRegularizedDotLogits_eq_dotProductLogits_add_uniformShift_of_constantKeyNorm
            (E := E) (V := V) q ctx β κ hκ]
          exact softmax_add_uniformShift (n := Fin n)
            (x := dotProductLogits (E := E) (V := V) q ctx β)
            (c := β * (-(1 / 2 : ℝ) * κ))
    _ = fun i => euclideanAttentionWeights q ctx β i := by
          exact dotProductSoftmaxWeights_eq_euclideanAttentionWeights (E := E) (V := V) q ctx β

-- theorem-class: bridge
/-- Under constant key norm, the positive-sheet split attention head is exactly Euclidean. -/
theorem polarizedPlusAttentionHead_eq_euclideanAttentionHead_of_constantKeyNorm
    (q : E) (ctx : ContextWindow n E V) (β κ : ℝ)
    (hκ : ∀ i, ‖ctx.keys i‖ ^ 2 = κ) :
    polarizedPlusAttentionHead (E := E) (V := V) q ctx β
      = euclideanAttentionHead q ctx β := by
  unfold polarizedPlusAttentionHead euclideanAttentionHead attentionHead
  simp [polarizedPlusAttentionWeights_eq_euclideanAttentionWeights_of_constantKeyNorm
    (E := E) (V := V) (q := q) (ctx := ctx) (β := β) (κ := κ) hκ]

end InfoGeometry.Canonical.Attention
