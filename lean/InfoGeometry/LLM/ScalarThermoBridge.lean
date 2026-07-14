import InfoGeometry.LLM.ThermodynamicSwitching
import InfoGeometry.Convex.LogSumExp
import InfoGeometry.Canonical.LogSumExp
import InfoGeometry.ExponentialFamily.Analytic.LogSumExp
import InfoGeometry.Fenchel
import InfoGeometry.Canonical.SinkhornFoundation
import InfoGeometry.Meta.Architecture

open scoped BigOperators InnerProductSpace

namespace ScalarThermoBridge

open InfoGeometry.Canonical.MoE

section RouterScalarBridges

variable {Tok V : Type*} [Fintype Tok] [DecidableEq Tok]
variable [NormedAddCommGroup V] [NormedSpace ℝ V]
variable {n : Nat}

/-- Router logits induced by inverse-temperature and energy. -/
noncomputable def routerLogits (β : ℝ) (x : Tok → V) (i : Tok) : ExpertIdx n → ℝ :=
  fun e => -β * routerEnergy n x i e

section RouterOmitted

omit [Fintype Tok] [DecidableEq Tok] [NormedSpace ℝ V]

/-- Router partition is the finite convex log-sum-exp partition of router logits. -/
@[rep_depth transport]
theorem routerPartition_eq_convex_sumExp (β : ℝ) (x : Tok → V) (i : Tok) :
    routerPartition n β x i
      = InfoGeometry.Convex.LogSumExp.sumExp (n := ExpertIdx n) (routerLogits (n := n) β x i) := by
  unfold InfoGeometry.Convex.LogSumExp.sumExp routerPartition unnormalizedWeights routerLogits
  refine Finset.sum_congr rfl ?_
  intro e he
  rfl

/-- The router log-partition is the convex `lse` potential on router logits. -/
@[rep_depth transport]
theorem logSumExpRouter_eq_convex_lse (β : ℝ) (x : Tok → V) (i : Tok) :
    InfoGeometry.LLM.ThermodynamicSwitching.logSumExpRouter (n := n) β x i
      = InfoGeometry.Convex.LogSumExp.lse (n := ExpertIdx n) (routerLogits (n := n) β x i) := by
  unfold InfoGeometry.LLM.ThermodynamicSwitching.logSumExpRouter InfoGeometry.Convex.LogSumExp.lse
  rw [routerPartition_eq_convex_sumExp (n := n) β x i]

/-- Normalized router weights coincide with convex softmax of router logits. -/
@[rep_depth transport]
theorem normalizedWeights_eq_convex_softmax
    (β : ℝ) (x : Tok → V) (i : Tok) (e : ExpertIdx n) :
    normalizedWeights n β x i e
      = InfoGeometry.Convex.LogSumExp.softmax (n := ExpertIdx n) (routerLogits (n := n) β x i) e := by
  unfold normalizedWeights unnormalizedWeights InfoGeometry.Convex.LogSumExp.softmax
    routerLogits
  rw [routerPartition_eq_convex_sumExp (n := n) β x i]
  rfl

/-- Convex softmax on router logits is invariant under uniform additive shifts. -/
@[rep_depth transport]
theorem convex_softmax_routerLogits_add_uniformShift
    [Nonempty (Fin n)] (β c : ℝ) (x : Tok → V) (i : Tok) :
    InfoGeometry.Convex.LogSumExp.softmax
        (n := ExpertIdx n)
        ((routerLogits (n := n) β x i)
          + c • InfoGeometry.Convex.LogSumExp.uniformShift (n := ExpertIdx n))
      = InfoGeometry.Convex.LogSumExp.softmax (n := ExpertIdx n) (routerLogits (n := n) β x i) := by
  simpa using
    (InfoGeometry.Convex.LogSumExp.softmax_add_uniformShift
      (n := ExpertIdx n) (x := routerLogits (n := n) β x i) c)

/-- Router partition is the analytic weighted log-sum-exp partition with unit base weights. -/
@[rep_depth transport]
theorem routerPartition_eq_analytic_logSumExpPartition
    (β : ℝ) (x : Tok → V) (i : Tok) :
    routerPartition n β x i
      = InfoGeometry.Analytic.logSumExpPartition
          (w := fun _ : ExpertIdx n => (1 : ℝ))
          (a := fun e => -routerEnergy n x i e)
          β := by
  unfold InfoGeometry.Analytic.logSumExpPartition routerPartition unnormalizedWeights
  refine Finset.sum_congr rfl ?_
  intro e he
  ring_nf

/-- Router log-partition coincides with analytic finite `logSumExp` at unit base weights. -/
@[rep_depth transport]
theorem logSumExpRouter_eq_analytic_logSumExp
    (β : ℝ) (x : Tok → V) (i : Tok) :
    InfoGeometry.LLM.ThermodynamicSwitching.logSumExpRouter (n := n) β x i
      = InfoGeometry.Analytic.logSumExp
          (w := fun _ : ExpertIdx n => (1 : ℝ))
          (a := fun e => -routerEnergy n x i e)
          β := by
  unfold InfoGeometry.LLM.ThermodynamicSwitching.logSumExpRouter
    InfoGeometry.Analytic.logSumExp
  rw [routerPartition_eq_analytic_logSumExpPartition (n := n) β x i]

/-- Router normalized weights coincide with analytic Gibbs/log-sum-exp weights. -/
@[rep_depth transport]
theorem normalizedWeights_eq_analytic_logSumExpWeight
    (β : ℝ) (x : Tok → V) (i : Tok) (e : ExpertIdx n) :
    normalizedWeights n β x i e
      = InfoGeometry.Analytic.logSumExpWeight
          (w := fun _ : ExpertIdx n => (1 : ℝ))
          (a := fun j => -routerEnergy n x i j)
          β e := by
  unfold normalizedWeights unnormalizedWeights InfoGeometry.Analytic.logSumExpWeight
  rw [routerPartition_eq_analytic_logSumExpPartition (n := n) β x i]
  ring_nf

end RouterOmitted

end RouterScalarBridges

section SinkhornGaugeBridge

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
variable (n : Nat) [Nonempty (Fin n)]

section SinkhornOmitted

omit [NormedSpace ℝ V]

/-- LLM-facing alias: router switch matrix is row-stochastic (simplex-normalized rows). -/
@[rep_depth transport]
theorem switchMatrix_mem_rowStochastic_bridge
    (β : ℝ) (x : Fin n → V) :
    switchMatrix n β x ∈ Matrix.rowStochastic ℝ (Fin n) := by
  simpa using InfoGeometry.Canonical.MoE.switchMatrix_mem_rowStochastic (n := n) β x

end SinkhornOmitted

end SinkhornGaugeBridge

section FenchelBridge

/-- LLM-lane alias of Fenchel nonnegativity (temperature-regularized convex gap). -/
@[rep_depth transport]
theorem fenchelGap_nonneg_bridge
    {f fStar : ℝ → ℝ}
    (hConj : InfoGeometry.Convex.OneD.IsLegendreConjugate f fStar)
    (θ η : ℝ) :
    0 ≤ InfoGeometry.Convex.OneD.fenchelGap f fStar θ η := by
  simpa using InfoGeometry.Convex.OneD.fenchelGap_nonneg_of_conjugate hConj θ η

end FenchelBridge

end ScalarThermoBridge
