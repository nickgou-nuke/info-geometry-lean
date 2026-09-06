import InfoGeometry.Canonical.GrandCanonicalExperts
import InfoGeometry.Canonical.SpectralInference
import InfoGeometry.Canonical.HyperbolicRotor
import InfoGeometry.Canonical.KreinDoubledAtom
import InfoGeometry.Canonical.MajoranaKitaevSpinorBridge
import InfoGeometry.Clifford.Hestenes
import InfoGeometry.Krein.DoubledSpace
import InfoGeometry.Meta.Architecture
import Mathlib.LinearAlgebra.Dimension.Constructions

open scoped BigOperators

/-!
# InfoGeometry.Canonical.GenerativeInferenceCore

Canonical owner surface for generative-inference lineage across:

1. routing/expert semantic state (`GrandCanonicalExperts`),
2. surprisal/parity entropy readouts (`GrandCanonicalExperts`),
3. Bayesian chain action (`SpectralInference`),
4. certified chiral spectral obstruction (`SpectralInference`).

This module does not replace those owners. It packages their interoperable
surface into one datum and exposes explicit bridge-candidate readouts.

Design note: the phase lane here is treated in real split-doubled form.
Hyperbolic rotor/boost channels are surfaced explicitly; no primitive complex
scalar ontology is introduced by this owner.
-/

namespace InfoGeometry.Canonical.GenerativeInferenceCore

open InfoGeometry.Canonical.MoE
open InfoGeometry.Canonical.SpectralInference
open InfoGeometry.Canonical.MajoranaKitaevSpinorBridge
open InfoGeometry.Convex

section Core

variable {n : Nat}
variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [FiniteDimensional ℝ E]

/-- Routing mode surface inherited from the permutation-mode MoE owner. -/
abbrev RoutingMode (n : Nat) := PermutationMode n

/-- Routing labels on permutation modes inherit the split Clifford labels. -/
abbrev RoutingLabel := CliffordLabel

/--
Unified generative-inference datum:
- mode routing weights and labels,
- Hessian geometry and Bayesian chain,
- certified chiral spectral package for anomaly/projector readout.
-/
structure GenerativeInferenceDatum (n : Nat) (E : Type*)
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [FiniteDimensional ℝ E] where
  routingWeights : RoutingMode n → ℝ
  routingLabels : RoutingMode n → RoutingLabel
  geometry : HessianGeometry E
  beliefChain : ℕ → E
  chiralPackage : CertifiedChiralSpectralTriple E

/-- Context-sensitive semantic state induced by routed permutation modes. -/
noncomputable def contextSemanticState
    (G : GenerativeInferenceDatum (n := n) (E := E)) : ℝ × ℝ :=
  permutationCliffordSemanticState G.routingWeights G.routingLabels

/-- `plus` channel mass of the routed semantic state. -/
noncomputable def plusChannelMass
    (G : GenerativeInferenceDatum (n := n) (E := E)) : ℝ :=
  plusMass G.routingWeights G.routingLabels

/-- `minus` channel mass of the routed semantic state. -/
noncomputable def minusChannelMass
    (G : GenerativeInferenceDatum (n := n) (E := E)) : ℝ :=
  minusMass G.routingWeights G.routingLabels

/-- Shannon-style surprisal entropy on routing weights. -/
noncomputable def routingEntropy
    (G : GenerativeInferenceDatum (n := n) (E := E)) : ℝ :=
  modeWeightEntropy G.routingWeights

/-- Coarse parity entropy from `plus/minus` routing channels. -/
noncomputable def routingParityEntropy
    (G : GenerativeInferenceDatum (n := n) (E := E)) : ℝ :=
  parityEntropy G.routingWeights G.routingLabels

/-- Mass-like routing coupling (`plus` channel minus `minus` channel). -/
noncomputable def routingMassCoupling
    (G : GenerativeInferenceDatum (n := n) (E := E)) : ℝ :=
  plusChannelMass G - minusChannelMass G

/-- Bayesian chain action up to horizon `N`. -/
noncomputable def bayesianChainAction
    (G : GenerativeInferenceDatum (n := n) (E := E)) (N : ℕ) : ℝ :=
  bayesianAction G.geometry G.beliefChain N

/--
Hyperbolic boost scale from the Hestenes split `Cl(1,1)` lane.
Numerically this is `exp θ`.
-/
noncomputable def hyperbolicBoostScale (θ : ℝ) : ℝ :=
  InfoGeometry.Clifford.Hestenes.expPseudoscalar θ

/-- Hyperbolically boosted Bayesian action. -/
noncomputable def hyperbolicallyBoostedBayesianAction
    (G : GenerativeInferenceDatum (n := n) (E := E))
    (θ : ℝ) (N : ℕ) : ℝ :=
  hyperbolicBoostScale θ * bayesianChainAction G N

/-- Certified Drazin spectral projector of the generative-inference datum. -/
abbrev spectralProjector
    (G : GenerativeInferenceDatum (n := n) (E := E)) : E →L[ℝ] E :=
  CertifiedChiralSpectralTriple.spectralProjector G.chiralPackage

/-- Certified Moore-Penrose metric projector of the generative-inference datum. -/
abbrev metricProjector
    (G : GenerativeInferenceDatum (n := n) (E := E)) : E →L[ℝ] E :=
  CertifiedChiralSpectralTriple.metricProjector G.chiralPackage

/-- Certified spectral obstruction operator (projector commutator). -/
noncomputable abbrev spectralObstructionOperator
    (G : GenerativeInferenceDatum (n := n) (E := E)) : E →L[ℝ] E :=
  CertifiedChiralSpectralTriple.chiralAnomalyOperator G.chiralPackage

/-- Certified scalar anomaly scale attached to the chiral package. -/
noncomputable def anomalyScale
    (G : GenerativeInferenceDatum (n := n) (E := E)) : ℝ :=
  CertifiedChiralSpectralTriple.epsilon G.chiralPackage

lemma contextSemanticState_fst_eq_plusChannelMass
    (G : GenerativeInferenceDatum (n := n) (E := E)) :
    (contextSemanticState G).1 = plusChannelMass G := by
  simpa [contextSemanticState, plusChannelMass] using
    (cliffordSemanticState_fst_eq_plusMass G.routingWeights G.routingLabels)

lemma contextSemanticState_snd_eq_minusChannelMass
    (G : GenerativeInferenceDatum (n := n) (E := E)) :
    (contextSemanticState G).2 = minusChannelMass G := by
  simpa [contextSemanticState, minusChannelMass] using
    (cliffordSemanticState_snd_eq_minusMass G.routingWeights G.routingLabels)

lemma contextSemanticState_coord_sum_eq_weight_sum
    (G : GenerativeInferenceDatum (n := n) (E := E)) :
    (contextSemanticState G).1 + (contextSemanticState G).2
      = ∑ σ : RoutingMode n, G.routingWeights σ := by
  simpa [contextSemanticState, RoutingMode] using
    (cliffordSemanticState_coord_sum_eq_weight_sum G.routingWeights G.routingLabels)

theorem bayesianChainAction_nonneg
    (G : GenerativeInferenceDatum (n := n) (E := E)) (N : ℕ) :
    0 ≤ bayesianChainAction G N := by
  simpa [bayesianChainAction] using
    (bayesianAction_nonneg (H := G.geometry) (γ := G.beliefChain) (N := N))

lemma routingMassCoupling_eq_coord_diff
    (G : GenerativeInferenceDatum (n := n) (E := E)) :
    routingMassCoupling G = (contextSemanticState G).1 - (contextSemanticState G).2 := by
  simp [routingMassCoupling, contextSemanticState_fst_eq_plusChannelMass,
    contextSemanticState_snd_eq_minusChannelMass]

theorem hyperbolicBoostScale_eq_exp (θ : ℝ) :
    hyperbolicBoostScale θ = Real.exp θ := by
  simpa [hyperbolicBoostScale] using
    (InfoGeometry.Clifford.Hestenes.expPseudoscalar_is_scaling θ)

theorem hyperbolicallyBoostedBayesianAction_nonneg
    (G : GenerativeInferenceDatum (n := n) (E := E))
    (θ : ℝ) (N : ℕ) :
    0 ≤ hyperbolicallyBoostedBayesianAction G θ N := by
  have hScale : 0 ≤ hyperbolicBoostScale θ := by
    rw [hyperbolicBoostScale_eq_exp]
    exact le_of_lt (Real.exp_pos θ)
  exact mul_nonneg hScale (bayesianChainAction_nonneg (G := G) N)

theorem spectralObstruction_eq_zero_iff_projectors_commute
    (G : GenerativeInferenceDatum (n := n) (E := E)) :
    spectralObstructionOperator G = 0 ↔
      spectralProjector G * metricProjector G
        = metricProjector G * spectralProjector G := by
  simpa [spectralObstructionOperator, spectralProjector, metricProjector] using
    (CertifiedChiralSpectralTriple.chiralAnomalyOperator_eq_zero_iff_projectors_commute
      (CCST := G.chiralPackage))

theorem anomalyScale_eq_zero_of_projectors_commute
    (G : GenerativeInferenceDatum (n := n) (E := E))
    (hComm :
      spectralProjector G * metricProjector G
        = metricProjector G * spectralProjector G) :
    anomalyScale G = 0 := by
  simpa [anomalyScale, spectralProjector, metricProjector] using
    (CertifiedChiralSpectralTriple.epsilon_eq_zero_of_projectors_commute
      (CCST := G.chiralPackage) hComm)

/--
Bridge-candidate payload assembled from the unified generative-inference core.

This is the single owner readout carrying:
- routed semantic state and channel masses,
- routing surprisal/parity entropy,
- Bayesian chain action at a horizon,
- certified spectral obstruction operator.
-/
structure BridgeCandidate (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] where
  semanticState : ℝ × ℝ
  plusMass : ℝ
  minusMass : ℝ
  massCoupling : ℝ
  modeEntropy : ℝ
  parityEntropy : ℝ
  chainAction : ℝ
  boostedChainAction : ℝ
  anomalyOperator : E →L[ℝ] E

noncomputable def bridgeCandidate
    (G : GenerativeInferenceDatum (n := n) (E := E))
    (θ : ℝ) (N : ℕ) : BridgeCandidate E :=
  { semanticState := contextSemanticState G
    plusMass := plusChannelMass G
    minusMass := minusChannelMass G
    massCoupling := routingMassCoupling G
    modeEntropy := routingEntropy G
    parityEntropy := routingParityEntropy G
    chainAction := bayesianChainAction G N
    boostedChainAction := hyperbolicallyBoostedBayesianAction G θ N
    anomalyOperator := spectralObstructionOperator G }

theorem bridgeCandidate_chainAction_nonneg
    (G : GenerativeInferenceDatum (n := n) (E := E))
    (θ : ℝ) (N : ℕ) :
    0 ≤ (bridgeCandidate G θ N).chainAction := by
  simpa [bridgeCandidate] using bayesianChainAction_nonneg (G := G) N

theorem bridgeCandidate_boostedChainAction_nonneg
    (G : GenerativeInferenceDatum (n := n) (E := E))
    (θ : ℝ) (N : ℕ) :
    0 ≤ (bridgeCandidate G θ N).boostedChainAction := by
  simpa [bridgeCandidate] using
    hyperbolicallyBoostedBayesianAction_nonneg (G := G) θ N

end Core

section BistochasticLift

variable {V : Type*} [NormedAddCommGroup V]
variable (n : Nat) [Nonempty (Fin n)]

/--
Existence lift from bistochastic routing to a normalized context semantic state.
-/
theorem exists_contextSemanticState_of_bistochastic
    (β : ℝ) (x : Fin n → V) (hcol : IsBistochasticSwitch n β x)
    (label : RoutingMode n → RoutingLabel) :
    ∃ w : RoutingMode n → ℝ,
      (∀ σ, 0 ≤ w σ) ∧
      ∑ σ, w σ = 1 ∧
      ∑ σ, w σ • σ.permMatrix ℝ = switchMatrix n β x ∧
      let ψ := permutationCliffordSemanticState w label
      0 ≤ ψ.1 ∧ 0 ≤ ψ.2 ∧ ψ.1 + ψ.2 = 1 := by
  simpa [RoutingMode, RoutingLabel] using
    (exists_clifford_labeled_state_of_bistochastic
      (n := n) β x hcol label)

/--
The same bistochastic lift can be chosen with nonnegative context semantic
coordinates.
-/
theorem exists_contextSemanticState_of_bistochastic_nonneg
    (β : ℝ) (x : Fin n → V) (hcol : IsBistochasticSwitch n β x)
    (label : RoutingMode n → RoutingLabel) :
    ∃ w : RoutingMode n → ℝ,
      (∀ σ, 0 ≤ w σ) ∧
      ∑ σ, w σ = 1 ∧
      ∑ σ, w σ • σ.permMatrix ℝ = switchMatrix n β x ∧
      let ψ := permutationCliffordSemanticState w label
      0 ≤ ψ.1 ∧ 0 ≤ ψ.2 := by
  rcases exists_clifford_labeled_state_of_bistochastic (n := n) β x hcol label with
    ⟨w, hw_nonneg, hw_sum, hw_matrix, hψ⟩
  refine ⟨w, hw_nonneg, hw_sum, hw_matrix, ?_⟩
  dsimp
  exact ⟨hψ.1, hψ.2.left⟩

end BistochasticLift

section SplitDoubledLane

variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [FiniteDimensional ℝ E]

/-- Canonical split doubled carrier (`E ⊕ E`) on the `L²` lane. -/
abbrev SplitDoubledCarrier (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] : Type _ :=
  InfoGeometry.Krein.DoubledSpace E

/-- Canonical doubled atom on the split carrier (`J`, `ε`, `K = Jε`). -/
noncomputable def splitDoubledAtom :
    InfoGeometry.Canonical.KreinDoubledAtom :=
  InfoGeometry.Canonical.cl11DoubledAtom E

omit [FiniteDimensional ℝ E] in
@[simp] theorem splitDoubledAtom_phaseAxis_sq :
    (splitDoubledAtom (E := E)).K.comp (splitDoubledAtom (E := E)).K
      = -(LinearMap.id : splitDoubledAtom (E := E) →ₗ[ℝ] splitDoubledAtom (E := E)) := by
  simpa [splitDoubledAtom] using
    (InfoGeometry.Canonical.KreinDoubledAtom.K_sq_eq_neg_id
      (InfoGeometry.Canonical.cl11DoubledAtom E))

/-- Dimension closure: doubled lane has exactly twice the base real dimension. -/
theorem splitDoubledCarrier_finrank_eq_two_mul_finrank :
    Module.finrank ℝ (SplitDoubledCarrier E) = 2 * Module.finrank ℝ E := by
  let e :
      SplitDoubledCarrier E ≃ₗ[ℝ] E × E :=
    (WithLp.prodContinuousLinearEquiv (p := (2 : ENNReal)) ℝ E E).toLinearEquiv
  calc
    Module.finrank ℝ (SplitDoubledCarrier E)
        = Module.finrank ℝ (E × E) := LinearEquiv.finrank_eq e
    _ = Module.finrank ℝ E + Module.finrank ℝ E := Module.finrank_prod (R := ℝ) (M := E) (M' := E)
    _ = 2 * Module.finrank ℝ E := by ring

/-- Specialized closure for the `64 ⊕ 64` split carrier (`128`). -/
theorem splitDoubledCarrier_finrank_eq_128_of_finrank_eq_64
    (h64 : Module.finrank ℝ E = 64) :
    Module.finrank ℝ (SplitDoubledCarrier E) = 128 := by
  calc
    Module.finrank ℝ (SplitDoubledCarrier E)
        = 2 * Module.finrank ℝ E := splitDoubledCarrier_finrank_eq_two_mul_finrank (E := E)
    _ = 2 * 64 := by simp [h64]
    _ = 128 := by norm_num

end SplitDoubledLane

section WeylMassLane

variable {S : Type*}
variable [NormedAddCommGroup S] [InnerProductSpace ℝ S] [CompleteSpace S] [FiniteDimensional ℝ S]
variable (M : InfoGeometry.Quantum.RealMajorana.RealMajoranaDatum (S := S))
variable (Q : S →L[ℝ] S)

/--
Mass-like Weyl coupling on the real doubled carrier:
norm imbalance between Weyl-plus and Weyl-minus zero modes.
-/
noncomputable def weylMassLikeCoupling
    (W : WeylBoundarySpinorPair (S := S) M Q) : ℝ :=
  ‖W.psiPlus‖ - ‖W.psiMinus‖

omit [CompleteSpace S] [FiniteDimensional ℝ S] in
theorem weylMassLikeCoupling_eq_zero_iff_balanced
    (W : WeylBoundarySpinorPair (S := S) M Q) :
    weylMassLikeCoupling M Q W = 0 ↔ ‖W.psiPlus‖ = ‖W.psiMinus‖ := by
  simpa [weylMassLikeCoupling] using
    (sub_eq_zero : ‖W.psiPlus‖ - ‖W.psiMinus‖ = 0 ↔ ‖W.psiPlus‖ = ‖W.psiMinus‖)

end WeylMassLane

section RotorLane

/-- Canonical hyperbolic boost rotor on the split Clifford tensor lane. -/
noncomputable def canonicalHyperbolicBoostRotor (n : ℕ) (θ : ℝ) :
    InfoGeometry.Canonical.SplitCliffordTensorBridge.SplitClNNTensorStep n :=
  InfoGeometry.Canonical.HyperbolicRotor.hyperbolicRotor n θ

@[simp] theorem canonicalHyperbolicBoostRotor_zero (n : ℕ) :
    canonicalHyperbolicBoostRotor n 0
      = (1 : InfoGeometry.Canonical.SplitCliffordTensorBridge.SplitClNNTensorStep n) := by
  unfold canonicalHyperbolicBoostRotor
  exact InfoGeometry.Canonical.HyperbolicRotor.hyperbolicRotor_zero n

end RotorLane

end InfoGeometry.Canonical.GenerativeInferenceCore
