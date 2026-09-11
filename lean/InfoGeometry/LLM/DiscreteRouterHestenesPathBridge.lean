import InfoGeometry.LLM.DiscreteRouterBayesStep
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.HestenesGibbsPathIntegral
import InfoGeometry.Meta.Architecture

open scoped BigOperators InnerProductSpace

namespace InfoGeometry.LLM

open DiscreteRouterBayesStep
open InfoGeometry.LLM.ScalarThermoBridge
open InfoGeometry.Canonical.MoE
open InfoGeometry.Canonical.PathIntegral

section PathGibbsBridge

variable {Tok V : Type 0} [Fintype Tok] [DecidableEq Tok]
variable [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
variable {n : Nat} [Nonempty (Fin n)]

local notation "H₂" => InfoGeometry.Krein.DoubledSpace V
local notation "EndH" => H₂ →L[ℝ] H₂

/-- Expert logits induced by Hestenes-Gibbs path surprisal on the doubled lane. -/
noncomputable def pathSurprisalLogits
    (β : ℝ) (K : EndH) (paths : ExpertIdx n → TacticPath (E := V)) : ExpertIdx n → ℝ :=
  fun e => -β * pathSurprisal (E := V) K (paths e)

/--
Normalized Gibbs router on expert-indexed path families.
This is the path-ensemble readout surface used to compare against Bayes routing.
-/
noncomputable def pathGibbsRouterUpdate
    (β : ℝ) (K : EndH) (paths : ExpertIdx n → TacticPath (E := V)) : ExpertIdx n → ℝ :=
  InfoGeometry.Convex.LogSumExp.softmax
    (n := ExpertIdx n) (pathSurprisalLogits (n := n) β K paths)

/--
Path Gibbs router is invariant under uniform additive shifts of path surprisal
logits (same softmax gauge invariance as the Bayes lane).
-/
@[rep_depth transport]
theorem pathGibbsRouterUpdate_eq_softmax_shift
    (β c : ℝ) (K : EndH) (paths : ExpertIdx n → TacticPath (E := V)) :
    pathGibbsRouterUpdate (n := n) β K paths
      =
    InfoGeometry.Convex.LogSumExp.softmax
      (n := ExpertIdx n)
      ((pathSurprisalLogits (n := n) β K paths)
        + c • InfoGeometry.Convex.LogSumExp.uniformShift (n := ExpertIdx n)) := by
  let _ : CompleteSpace V := inferInstance
  calc
    pathGibbsRouterUpdate (n := n) β K paths
        =
      InfoGeometry.Convex.LogSumExp.softmax
        (n := ExpertIdx n) (pathSurprisalLogits (n := n) β K paths) := by
          rfl
    _ =
      InfoGeometry.Convex.LogSumExp.softmax
        (n := ExpertIdx n)
        ((pathSurprisalLogits (n := n) β K paths)
          + c • InfoGeometry.Convex.LogSumExp.uniformShift (n := ExpertIdx n)) := by
            symm
            exact
              InfoGeometry.Convex.LogSumExp.softmax_add_uniformShift
                (n := ExpertIdx n)
                (x := pathSurprisalLogits (n := n) β K paths)
                c

/-- Path Gibbs router update is simplex-normalized. -/
@[rep_depth transport]
theorem pathGibbsRouterUpdate_preserves_simplex
    (β : ℝ) (K : EndH) (paths : ExpertIdx n → TacticPath (E := V)) :
    ∑ e : ExpertIdx n, pathGibbsRouterUpdate (n := n) β K paths e = 1 := by
  let _ : CompleteSpace V := inferInstance
  simpa [pathGibbsRouterUpdate] using
    (InfoGeometry.Convex.LogSumExp.sum_softmax_eq_one
      (n := ExpertIdx n)
      (x := pathSurprisalLogits (n := n) β K paths))

/--
At unit inverse-temperature, pointwise Gibbs path weights match canonical
`gibbsWeight` on each expert path.
-/
@[rep_depth transport]
theorem pathSurprisalLogits_exp_beta_one
    (K : EndH) (paths : ExpertIdx n → TacticPath (E := V)) (e : ExpertIdx n) :
    Real.exp (pathSurprisalLogits (n := n) (β := (1 : ℝ)) K paths e)
      = gibbsWeight (E := V) K (paths e) := by
  let _ : CompleteSpace V := inferInstance
  let _ : Nonempty (Fin n) := inferInstance
  simp [pathSurprisalLogits, gibbsWeight]

section OmitEnergyMatchVars

omit [Fintype Tok] [DecidableEq Tok] [Nonempty (Fin n)]

/--
If router energies coincide with path surprisals expertwise, Bayes routing equals
path Gibbs routing.
-/
@[rep_depth transport]
theorem bayesRouterUpdate_eq_pathGibbsRouterUpdate_of_energy_match
    (β : ℝ) (x : Tok → V) (i : Tok)
    (K : EndH) (paths : ExpertIdx n → TacticPath (E := V))
    (hMatch : ∀ e, routerEnergy n x i e = pathSurprisal (E := V) K (paths e)) :
    bayesRouterUpdate (n := n) β x i
      = pathGibbsRouterUpdate (n := n) β K paths := by
  let _ : CompleteSpace V := inferInstance
  funext e
  calc
    bayesRouterUpdate (n := n) β x i e
        =
      InfoGeometry.Convex.LogSumExp.softmax
        (n := ExpertIdx n) (routerLogits (n := n) β x i) e := by
          simpa [bayesRouterUpdate] using
            (normalizedWeights_eq_convex_softmax
              (n := n) (β := β) (x := x) (i := i) (e := e))
    _ =
      InfoGeometry.Convex.LogSumExp.softmax
        (n := ExpertIdx n)
        (pathSurprisalLogits (n := n) β K paths) e := by
          congr 1
          funext j
          simp [routerLogits, pathSurprisalLogits, hMatch j]
    _ = pathGibbsRouterUpdate (n := n) β K paths e := by
          rfl

/--
Symmetric restatement: path Gibbs router equals Bayes router under expertwise
energy↔surprisal matching.
-/
@[rep_depth transport]
theorem pathGibbsRouterUpdate_eq_bayesRouterUpdate_of_energy_match
    (β : ℝ) (x : Tok → V) (i : Tok)
    (K : EndH) (paths : ExpertIdx n → TacticPath (E := V))
    (hMatch : ∀ e, routerEnergy n x i e = pathSurprisal (E := V) K (paths e)) :
    pathGibbsRouterUpdate (n := n) β K paths
      = bayesRouterUpdate (n := n) β x i := by
  symm
  exact bayesRouterUpdate_eq_pathGibbsRouterUpdate_of_energy_match
    (n := n) (β := β) (x := x) (i := i) (K := K) (paths := paths) hMatch

end OmitEnergyMatchVars

end PathGibbsBridge

end InfoGeometry.LLM
