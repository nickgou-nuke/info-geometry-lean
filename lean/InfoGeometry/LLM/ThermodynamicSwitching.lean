import InfoGeometry.LLM.TransformerArchitecture
import InfoGeometry.Canonical.MixtureOfExperts
import InfoGeometry.Canonical.GrandCanonicalExperts
import InfoGeometry.Canonical.ArnoldMajoranaNetwork
import InfoGeometry.Canonical.ArnoldNetworkPresentation
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

omit [Fintype Tok] [DecidableEq Tok] [NormedSpace ℝ V] in
/-- Router partition is exactly the exponential of log-sum-exp. -/
@[rep_depth transport]
theorem routerPartition_eq_exp_logSumExp (β : ℝ) (x : Tok → V) (i : Tok) :
    routerPartition n β x i = Real.exp (logSumExpRouter (n := n) β x i) := by
  unfold logSumExpRouter
  rw [Real.exp_log (routerPartition_pos (n := n) β x i)]

/-- Boolean expert mask for gated/all-top switching. -/
abbrev SwitchMask (n : Nat) := ExpertIdx n → Bool

namespace SwitchMask

abbrev active {n : Nat} (mask : SwitchMask n) : ExpertIdx n → Bool :=
  mask

end SwitchMask

/-- All-top mode keeps every expert active. -/
def allTopMask (n : Nat) : SwitchMask n :=
  fun _ => true

/-- Masked thermodynamic routing weight. -/
noncomputable def maskedNormalizedWeight
    (mask : SwitchMask n) (β : ℝ) (x : Tok → V) (i : Tok) (e : ExpertIdx n) : ℝ :=
  if mask.active e then normalizedWeights n β x i e else 0

/-- Masked thermodynamic mixture output. -/
noncomputable def maskedNormalizedMixture
    (layer : MoELayer n V) (mask : SwitchMask n) (β : ℝ) (x : Tok → V) (i : Tok) : V :=
  ∑ e : ExpertIdx n,
    (maskedNormalizedWeight (n := n) mask β x i e) • (layer.experts e).apply (x i)

omit [Fintype Tok] [DecidableEq Tok] [NormedSpace ℝ V] in
/-- Masked weights remain nonnegative. -/
lemma maskedNormalizedWeight_nonneg
    (mask : SwitchMask n) (β : ℝ) (x : Tok → V) (i : Tok) (e : ExpertIdx n) :
    0 ≤ maskedNormalizedWeight (n := n) mask β x i e := by
  unfold maskedNormalizedWeight
  split_ifs with hActive
  · unfold normalizedWeights unnormalizedWeights
    exact div_nonneg (le_of_lt (Real.exp_pos _)) (le_of_lt (routerPartition_pos (n := n) β x i))
  · simp

omit [Fintype Tok] [DecidableEq Tok] [Nonempty (Fin n)] in
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

omit [Fintype Tok] [DecidableEq Tok] [NormedSpace ℝ V] in
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
open InfoGeometry.Canonical.QuantumPresentation

variable {E : Type}
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

/--
LLM-facing view of Arnold routing as a `QuantumPresentation` instance.

This is a direct translator call; it does not duplicate owner logic.
-/
@[rep_depth operator]
noncomputable def arnoldQuantumPresentation
    (n : Nat)
    (net : InfoGeometry.Canonical.MoE.ArnoldMajoranaNetwork n E)
    (β : ℝ) : Presentation :=
  InfoGeometry.Canonical.ArnoldNetworkPresentation.toQuantumPresentation
    (E := E) n net β

/-- Tagged representation property for the Arnold network lane in LLM space. -/
@[rep_depth operator]
noncomputable def arnoldTaggedPresentation
    (n : Nat)
    (net : InfoGeometry.Canonical.MoE.ArnoldMajoranaNetwork n E)
    (β : ℝ) : TaggedPresentation :=
  InfoGeometry.Canonical.ArnoldNetworkPresentation.taggedPresentation
    (E := E) n net β

@[rep_depth operator]
theorem arnoldTaggedPresentation_lane
    (n : Nat)
    (net : InfoGeometry.Canonical.MoE.ArnoldMajoranaNetwork n E)
    (β : ℝ) :
    (arnoldTaggedPresentation (E := E) n net β).lane = PresentationLane.arnoldNetwork := by
  rfl

/--
Generator bridge at the LLM interface boundary: the presentation generator is
exactly one-token Arnold routed output.
-/
@[rep_depth transport]
theorem arnoldQuantumPresentation_generator_eq_arnold
    (n : Nat)
    (net : InfoGeometry.Canonical.MoE.ArnoldMajoranaNetwork n E)
    (β : ℝ)
    (ψ : InfoGeometry.Canonical.ArnoldMajoranaCarrier E) :
    (arnoldQuantumPresentation (E := E) n net β).generator ψ
      = arnoldNetworkOutput (E := E) (n := n) net β (fun _ : Unit => ψ) () := by
  simpa [arnoldQuantumPresentation, arnoldNetworkOutput] using
    (InfoGeometry.Canonical.ArnoldNetworkPresentation.toQuantumPresentation_generator_eq_arnold
      (E := E) n net β ψ)

/--
Submodule-preservation bridge for the LLM-side presentation generator.
-/
@[rep_depth transport]
theorem arnoldQuantumPresentation_generator_mem_submodule
    (n : Nat)
    (net : InfoGeometry.Canonical.MoE.ArnoldMajoranaNetwork n E)
    (β : ℝ)
    (U : Submodule ℝ (InfoGeometry.Canonical.ArnoldMajoranaCarrier E))
    (ψ : InfoGeometry.Canonical.ArnoldMajoranaCarrier E)
    (hU : ∀ e : ExpertIdx n, ∀ v : InfoGeometry.Canonical.ArnoldMajoranaCarrier E,
      v ∈ U → (net.moe.experts e).apply v ∈ U)
    (hψ : ψ ∈ U) :
    (arnoldQuantumPresentation (E := E) n net β).generator ψ ∈ U := by
  simpa [arnoldQuantumPresentation] using
    (InfoGeometry.Canonical.ArnoldNetworkPresentation.arnoldGenerator_mem_submodule
      (E := E) n net β U ψ hU hψ)

end ArnoldBridge

end InfoGeometry.LLM.ThermodynamicSwitching
