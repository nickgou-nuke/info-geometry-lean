import InfoGeometry.LLM.ScalarThermoBridge
import InfoGeometry.Meta.Architecture

open scoped BigOperators InnerProductSpace

namespace InfoGeometry.LLM.DiscreteRouterBayesStep

open InfoGeometry.Canonical.MoE
open InfoGeometry.LLM.ScalarThermoBridge

section RouterBayesStep

variable {Tok V : Type*} [Fintype Tok] [DecidableEq Tok]
variable [NormedAddCommGroup V] [NormedSpace ℝ V]
variable {n : Nat} [Nonempty (Fin n)]

/-- Discrete Bayes router update on experts for token `i`. -/
noncomputable def bayesRouterUpdate
    (β : ℝ) (x : Tok → V) (i : Tok) : ExpertIdx n → ℝ :=
  fun e => normalizedWeights n β x i e

omit [Fintype Tok] [DecidableEq Tok] [NormedSpace ℝ V] in
/-- The Bayes router update is a simplex point (mass `1`). -/
@[rep_depth transport]
theorem bayes_router_update_preserves_simplex
    (β : ℝ) (x : Tok → V) (i : Tok) :
    ∑ e : ExpertIdx n, bayesRouterUpdate (n := n) β x i e = 1 := by
  simpa [bayesRouterUpdate] using normalizedWeights_sum_one (n := n) β x i

/--
The Bayes router update equals convex softmax on uniformly shifted router logits.
This is the additive-gauge invariance surface used by downstream discrete updates.
-/
@[rep_depth transport]
theorem bayes_router_update_eq_softmax_shift
    (β c : ℝ) (x : Tok → V) (i : Tok) :
    bayesRouterUpdate (n := n) β x i
      =
    InfoGeometry.Convex.LogSumExp.softmax
      (n := ExpertIdx n)
      ((routerLogits (n := n) β x i)
        + c • InfoGeometry.Convex.LogSumExp.uniformShift (n := ExpertIdx n)) := by
  calc
    bayesRouterUpdate (n := n) β x i
        =
      InfoGeometry.Convex.LogSumExp.softmax
        (n := ExpertIdx n) (routerLogits (n := n) β x i) := by
          funext e
          simpa [bayesRouterUpdate] using
            (normalizedWeights_eq_convex_softmax
              (n := n) (β := β) (x := x) (i := i) (e := e))
    _ =
      InfoGeometry.Convex.LogSumExp.softmax
        (n := ExpertIdx n)
        ((routerLogits (n := n) β x i)
          + c • InfoGeometry.Convex.LogSumExp.uniformShift (n := ExpertIdx n)) := by
            symm
            exact
              convex_softmax_routerLogits_add_uniformShift
                (n := n) (β := β) (c := c) (x := x) (i := i)

end RouterBayesStep

end InfoGeometry.LLM.DiscreteRouterBayesStep
