import InfoGeometry.LLM.TransformerArchitecture
import InfoGeometry.Canonical.MixtureOfExperts
import InfoGeometry.Canonical.GrandCanonicalExperts
import InfoGeometry.Canonical.ArnoldMajoranaNetwork
import InfoGeometry.Meta.Architecture

open scoped BigOperators InnerProductSpace

namespace InfoGeometry.LLM.ThermodynamicSwitching

open InfoGeometry.Canonical.MoE

section RouterSurface

variable {Tok V : Type*} [Fintype Tok] [DecidableEq Tok]
variable [NormedAddCommGroup V] [NormedSpace ℝ V]
variable {n : Nat} [Nonempty (Fin n)]

/-- Log-sum-exp surface of the thermodynamic router partition. -/
noncomputable def logSumExpRouter (β : ℝ) (x : Tok → V) (i : Tok) : ℝ :=
  Real.log (routerPartition n β x i)

/-- Router partition is exactly the exponential of log-sum-exp. -/
@[rep_depth transport]
theorem routerPartition_eq_exp_logSumExp (β : ℝ) (x : Tok → V) (i : Tok) :
    routerPartition n β x i = Real.exp (logSumExpRouter (n := n) β x i) := by
  unfold logSumExpRouter
  rw [Real.exp_log (routerPartition_pos (n := n) β x i)]

/-- Boolean expert mask for gated/all-top switching. -/
structure SwitchMask (n : Nat) where
  active : ExpertIdx n → Bool

/-- All-top mode keeps every expert active. -/
def allTopMask (n : Nat) : SwitchMask n where
  active := fun _ => true

/-- Masked thermodynamic routing weight. -/
noncomputable def maskedNormalizedWeight
    (mask : SwitchMask n) (β : ℝ) (x : Tok → V) (i : Tok) (e : ExpertIdx n) : ℝ :=
  if mask.active e then normalizedWeights n β x i e else 0

/-- Masked thermodynamic mixture output. -/
noncomputable def maskedNormalizedMixture
    (layer : MoELayer n V) (mask : SwitchMask n) (β : ℝ) (x : Tok → V) (i : Tok) : V :=
  ∑ e : ExpertIdx n,
    (maskedNormalizedWeight (n := n) mask β x i e) • (layer.experts e).apply (x i)

/-- Masked weights remain nonnegative. -/
lemma maskedNormalizedWeight_nonneg
    (mask : SwitchMask n) (β : ℝ) (x : Tok → V) (i : Tok) (e : ExpertIdx n) :
    0 ≤ maskedNormalizedWeight (n := n) mask β x i e := by
  unfold maskedNormalizedWeight
  split_ifs with hActive
  · unfold normalizedWeights unnormalizedWeights
    exact div_nonneg (le_of_lt (Real.exp_pos _)) (le_of_lt (routerPartition_pos (n := n) β x i))
  · simp

/-- All-top mask recovers the canonical normalized mixture. -/
@[rep_depth transport]
theorem maskedNormalizedMixture_allTop_eq_normalizedMixture
    (layer : MoELayer n V) (β : ℝ) (x : Tok → V) (i : Tok) :
    maskedNormalizedMixture (n := n) layer (allTopMask n) β x i
      = normalizedMixture layer β x i := by
  unfold maskedNormalizedMixture maskedNormalizedWeight allTopMask normalizedMixture
  refine Finset.sum_congr rfl ?_
  intro e he
  simp

/-- All-top thermodynamic weights form a simplex point (sum to `1`). -/
@[rep_depth transport]
theorem allTop_weights_sum_one (β : ℝ) (x : Tok → V) (i : Tok) :
    ∑ e : ExpertIdx n,
      maskedNormalizedWeight (n := n) (allTopMask n) β x i e = 1 := by
  unfold maskedNormalizedWeight allTopMask
  simpa using normalizedWeights_sum_one (n := n) β x i

end RouterSurface

section BistochasticBridge

variable {V : Type*} [NormedAddCommGroup V]
variable (n : Nat) [Nonempty (Fin n)]

/--
LLM-facing bridge: a bistochastic switch admits a permutation-simplex Clifford representation.

This imports the canonical Birkhoff/Clifford owner theorem into the LLM lane.
-/
@[rep_depth transport]
theorem exists_modewiseClifford_rep_of_bistochastic_switch
    (β : ℝ) (x : Fin n → V) (hcol : IsBistochasticSwitch n β x)
    (S : SplitCliffordSuperData n) :
    ∃ w : PermMode n → ℝ,
      (∀ σ, 0 ≤ w σ) ∧
      ∑ σ, w σ = 1 ∧
      ∑ σ, w σ • σ.permMatrix ℝ = switchMatrix n β x ∧
      weightedModeCliffordState S w
        = weightedModeCliffordStatePlus S w + weightedModeCliffordStateMinus S w := by
  simpa using exists_modewiseClifford_rep_of_bistochastic (n := n) β x hcol S

end BistochasticBridge

section ArnoldBridge

open InfoGeometry.Quantum.RealMajorana

variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [FiniteDimensional ℝ E]

/-- LLM-lane alias of canonical Arnold-Majorana routed output. -/
noncomputable abbrev arnoldNetworkOutput (n : Nat)
    (net : InfoGeometry.Canonical.MoE.ArnoldMajoranaNetwork n E) (β : ℝ)
    {Tok : Type*} [Fintype Tok] [DecidableEq Tok]
    (x : Tok → InfoGeometry.Canonical.ArnoldMajoranaCarrier E)
    (i : Tok) : InfoGeometry.Canonical.ArnoldMajoranaCarrier E :=
  InfoGeometry.Canonical.MoE.arnoldNetworkOutput n net β x i

/--
LLM-facing preservation bridge:
if every expert preserves a submodule, Arnold-Majorana all-top mixing preserves it.
-/
@[rep_depth transport]
theorem arnoldNetwork_preserves_submodule_bridge
    (n : Nat)
    (net : InfoGeometry.Canonical.MoE.ArnoldMajoranaNetwork n E)
    (β : ℝ)
    {Tok : Type*} [Fintype Tok] [DecidableEq Tok]
    (U : Submodule ℝ (InfoGeometry.Canonical.ArnoldMajoranaCarrier E))
    (x : Tok → InfoGeometry.Canonical.ArnoldMajoranaCarrier E)
    (i : Tok)
    (hU : ∀ e : ExpertIdx n, ∀ v : InfoGeometry.Canonical.ArnoldMajoranaCarrier E,
      v ∈ U → (net.moe.experts e).apply v ∈ U)
    (hx : x i ∈ U) :
    arnoldNetworkOutput (n := n) net β x i ∈ U := by
  simpa [arnoldNetworkOutput] using
    (InfoGeometry.Canonical.MoE.arnoldNetwork_preserves_submodule (E := E)
      (n := n) (net := net) (β := β) (U := U) (x := x) (i := i) hU hx)

end ArnoldBridge

end InfoGeometry.LLM.ThermodynamicSwitching
