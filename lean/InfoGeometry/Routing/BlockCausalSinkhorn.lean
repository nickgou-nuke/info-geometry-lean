/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Routing.FiniteLogSinkhorn
import InfoGeometry.Routing.CausalPrefixPooling
import InfoGeometry.Routing.PrefixCausalDifferential

/-!
# Prefix noninterference for finite log-Sinkhorn readout

The prefix inputs are finite real-valued chunk summaries. The channel solver
is a fixed function of three local arguments. No inverse, convergence,
well-conditioning, or runtime refinement theorem is hidden in that type.
The final section instantiates the zero-derivative theorem on raw normed chunk
inputs using arbitrary pointwise encoders, without inventing norm instances
for the summary structure. The source readout and its row-normalized variant
are kept distinct. Causality is at chunk granularity.
-/

namespace InfoGeometry.Routing.BlockCausalSinkhorn

open Matrix
open scoped BigOperators
open InfoGeometry.Routing.FiniteLogSinkhorn

noncomputable section

variable {C L K D : Type*}
variable [Fintype C] [LinearOrder C]
variable [Fintype L] [Fintype K] [Fintype D]
variable [DecidableEq L] [DecidableEq K] [DecidableEq D]

/-!
## 4. Full Block-Causal Bipartite Sinkhorn Attention Pipeline & Zero Future Leakage
-/

/-- Per-chunk input bundle for `BlockCausalMultiHeadBipartiteSinkhornAttention`. -/
structure ChunkInput (L K D : Type*) where
  /-- Log-partition vector `m^{(s)} ∈ ℝ^K` of shape logits in chunk `s`. -/
  m_shape : K → ℝ
  /-- Local barycentric key centroids `K_chunk^{(s)} ∈ ℝ^{K × D}` of chunk `s`. -/
  K_chunk : Matrix K D ℝ
  /-- Local barycentric shape values `b_shape_chunk^{(s)} ∈ ℝ^{K × D}` of chunk `s`. -/
  V_shape : Matrix K D ℝ
  /-- Local detector query centroids `Q_lat^{(s)} ∈ ℝ^{K × D}` of chunk `s`. -/
  Q_lat   : Matrix K D ℝ
  /-- Local detector values `b_det^{(s)} ∈ ℝ^{K × D}` of chunk `s`. -/
  V_det   : Matrix K D ℝ
  /-- Unnormalized detector token-to-channel weights `V_chunk^{(s)} ∈ ℝ^{L × K}`. -/
  V_tok   : Matrix L K ℝ

/-- Per-chunk `K × K` log-coincidence matrix `logS^{(t)}` formed from the causal prefix
    key centroids `K_lat^{(≤ t)}` and current-chunk detector query centroids `Q_lat^{(t)}`. -/
noncomputable def blockCausalLogScore
    (x : C → ChunkInput L K D) (τ : ℝ) (Θ₀ : Matrix K K ℝ) (t : C) :
    Matrix K K ℝ :=
  let Ω := causalPrefixWeights (fun s => (x s).m_shape)
  let K_lat := causalPrefixPool Ω (fun s => (x s).K_chunk) t
  let Q_lat := (x t).Q_lat
  fun k l => (∑ d : D, K_lat k d * Q_lat l d) / τ + Θ₀ k l

/-- Full chunk-`t` output of Block-Causal Bipartite Sinkhorn Attention for any
    bipartite channel solver `Ψ : Matrix K K ℝ → Matrix K D ℝ → Matrix K D ℝ → Matrix K D ℝ`
    (such as `(1 - g) Bᵀ b_shape + g x_det` from the `2K × 2K` bipartite Laplacian). -/
noncomputable def blockCausalSinkhornChunkOutput
    (Ψ : Matrix K K ℝ → Matrix K D ℝ → Matrix K D ℝ → Matrix K D ℝ)
    (T : ℕ) (τ : ℝ) (Θ₀ : Matrix K K ℝ)
    (x : C → ChunkInput L K D) (t : C) : Matrix L D ℝ :=
  let Ω := causalPrefixWeights (fun s => (x s).m_shape)
  let b_shape_prefix := causalPrefixPool Ω (fun s => (x s).V_shape) t
  let logS := blockCausalLogScore x τ Θ₀ t
  let B_core := sinkhornMatrix T logS
  let d_det := sinkhornDetGain T logS
  let combined_det_lat := Ψ B_core b_shape_prefix (x t).V_det
  let V_calibrated : Matrix L K ℝ := fun j l => (x t).V_tok j l * d_det l
  V_calibrated * combined_det_lat

/-- **Main Forward Theorem (`blockCausalSinkhorn_zero_future_dependence`):**
    Block-lower-triangular causal pooling followed by per-chunk `T`-step Sinkhorn scaling
    and bipartite Laplacian readout at chunk `t` has identically ZERO dependence on
    future chunks `s > t`:
    1. If `x₁` and `x₂` agree on all chunks `s ≤ t`, then at chunk `t` their log-coincidence
       cores `logS`, Sinkhorn matrices `B^{(T)}`, channel gains `(d_shape, d_det)`, and
       decoded token outputs `Y^{(t)}` are identically equal.
    2. In particular, perturbing any future chunk `s₀ > t` (`Function.update x s₀ v`)
       leaves the chunk-`t` Sinkhorn matrix and output strictly unchanged. -/
theorem blockCausalSinkhorn_zero_future_dependence
    (Ψ : Matrix K K ℝ → Matrix K D ℝ → Matrix K D ℝ → Matrix K D ℝ)
    (T : ℕ) (τ : ℝ) (Θ₀ : Matrix K K ℝ)
    (x₁ x₂ : C → ChunkInput L K D) (t : C)
    (h_past : ∀ s ≤ t, x₁ s = x₂ s) :
    blockCausalLogScore x₁ τ Θ₀ t = blockCausalLogScore x₂ τ Θ₀ t ∧
    sinkhornMatrix T (blockCausalLogScore x₁ τ Θ₀ t) =
      sinkhornMatrix T (blockCausalLogScore x₂ τ Θ₀ t) ∧
    sinkhornShapeGain T (blockCausalLogScore x₁ τ Θ₀ t) =
      sinkhornShapeGain T (blockCausalLogScore x₂ τ Θ₀ t) ∧
    sinkhornDetGain T (blockCausalLogScore x₁ τ Θ₀ t) =
      sinkhornDetGain T (blockCausalLogScore x₂ τ Θ₀ t) ∧
    blockCausalSinkhornChunkOutput Ψ T τ Θ₀ x₁ t =
      blockCausalSinkhornChunkOutput Ψ T τ Θ₀ x₂ t := by
  have hm_eq : ∀ s ≤ t, (x₁ s).m_shape = (x₂ s).m_shape :=
    fun s hs => congrArg ChunkInput.m_shape (h_past s hs)
  have hK_eq : ∀ s ≤ t, (x₁ s).K_chunk = (x₂ s).K_chunk :=
    fun s hs => congrArg ChunkInput.K_chunk (h_past s hs)
  have hV_eq : ∀ s ≤ t, (x₁ s).V_shape = (x₂ s).V_shape :=
    fun s hs => congrArg ChunkInput.V_shape (h_past s hs)
  have hΩ_eq : ∀ s ≤ t,
      causalPrefixWeights (fun r => (x₁ r).m_shape) t s =
        causalPrefixWeights (fun r => (x₂ r).m_shape) t s := by
    intro s _
    ext k
    exact causalPrefixWeights_congr_of_le hm_eq s k
  have hΩ₁_causal : IsBlockCausalWeights (causalPrefixWeights (fun r => (x₁ r).m_shape)) :=
    (causalPrefixWeights_properties (fun r => (x₁ r).m_shape)).1
  have hΩ₂_causal : IsBlockCausalWeights (causalPrefixWeights (fun r => (x₂ r).m_shape)) :=
    (causalPrefixWeights_properties (fun r => (x₂ r).m_shape)).1
  have hK_pool :
      causalPrefixPool (causalPrefixWeights (fun r => (x₁ r).m_shape))
        (fun r => (x₁ r).K_chunk) t =
      causalPrefixPool (causalPrefixWeights (fun r => (x₂ r).m_shape))
        (fun r => (x₂ r).K_chunk) t :=
    causalPrefixPool_congr_of_le hΩ₁_causal hΩ₂_causal hΩ_eq hK_eq
  have hV_pool :
      causalPrefixPool (causalPrefixWeights (fun r => (x₁ r).m_shape))
        (fun r => (x₁ r).V_shape) t =
      causalPrefixPool (causalPrefixWeights (fun r => (x₂ r).m_shape))
        (fun r => (x₂ r).V_shape) t :=
    causalPrefixPool_congr_of_le hΩ₁_causal hΩ₂_causal hΩ_eq hV_eq
  have h_xt : x₁ t = x₂ t := h_past t (le_refl t)
  have h_logS : blockCausalLogScore x₁ τ Θ₀ t = blockCausalLogScore x₂ τ Θ₀ t := by
    unfold blockCausalLogScore
    dsimp only
    rw [hK_pool, h_xt]
  refine ⟨h_logS, by rw [h_logS], by rw [h_logS], by rw [h_logS], ?_⟩
  unfold blockCausalSinkhornChunkOutput
  dsimp only
  rw [hV_pool, h_logS, h_xt]

/-- **Future Single-Chunk Perturbation Corollary (`blockCausalSinkhorn_update_future_eq`):**
    Replacing the input at any future chunk `s₀ > t` with an arbitrary `v : ChunkInput L K D`
    leaves `blockCausalSinkhornChunkOutput` at chunk `t` strictly invariant. -/
theorem blockCausalSinkhorn_update_future_eq
    (Ψ : Matrix K K ℝ → Matrix K D ℝ → Matrix K D ℝ → Matrix K D ℝ)
    (T : ℕ) (τ : ℝ) (Θ₀ : Matrix K K ℝ)
    (x : C → ChunkInput L K D) {t s₀ : C} (hts₀ : t < s₀) (v : ChunkInput L K D) :
    blockCausalSinkhornChunkOutput Ψ T τ Θ₀ (Function.update x s₀ v) t =
      blockCausalSinkhornChunkOutput Ψ T τ Θ₀ x t := by
  apply (blockCausalSinkhorn_zero_future_dependence Ψ T τ Θ₀
    (Function.update x s₀ v) x t ?_).2.2.2.2
  intro s hs
  have h_ne : s ≠ s₀ := ne_of_lt (lt_of_le_of_lt hs hts₀)
  simp [Function.update, h_ne]

/-!
## 5. Zero Future Fréchet Derivative & Zero Backward Cotangent Pullback (`HasFDerivAt`)
-/

/-- `blockCausalSinkhornChunkOutput` is a valid `IsBlockCausalOperator`. -/
theorem blockCausalSinkhornChunkOutput_isBlockCausal
    (Ψ : Matrix K K ℝ → Matrix K D ℝ → Matrix K D ℝ → Matrix K D ℝ)
    (T : ℕ) (τ : ℝ) (Θ₀ : Matrix K K ℝ) :
    IsBlockCausalOperator (fun x t => blockCausalSinkhornChunkOutput Ψ T τ Θ₀ x t) :=
  fun t x₁ x₂ h_past =>
    (blockCausalSinkhorn_zero_future_dependence Ψ T τ Θ₀ x₁ x₂ t h_past).2.2.2.2

/-- Calibrated detector mass: this denominator is absent from the submitted
raw readout. It is local to the same current chunk and prefix. -/
def detectorMass (T : ℕ) (τ : ℝ) (Θ₀ : Matrix K K ℝ)
    (x : C → ChunkInput L K D) (t : C) (j : L) : ℝ :=
  ∑ l, (x t).V_tok j l * sinkhornDetGain T (blockCausalLogScore x τ Θ₀ t) l

/-- Row-normalized companion to the submitted, unnormalized readout.
Total real division defines this even on zero mass; stochastic interpretation
requires the positive-mass theorem below. -/
def normalizedChunkOutput
    (Ψ : Matrix K K ℝ → Matrix K D ℝ → Matrix K D ℝ → Matrix K D ℝ)
    (T : ℕ) (τ : ℝ) (Θ₀ : Matrix K K ℝ)
    (x : C → ChunkInput L K D) (t : C) : Matrix L D ℝ :=
  fun j d => blockCausalSinkhornChunkOutput Ψ T τ Θ₀ x t j d /
    detectorMass T τ Θ₀ x t j

/-- Positive current-chunk detector responses give positive calibrated mass. -/
theorem detectorMass_pos [Nonempty K]
    (T : ℕ) (τ : ℝ) (Θ₀ : Matrix K K ℝ)
    (x : C → ChunkInput L K D) (t : C) (j : L)
    (hpos : ∀ l, 0 < (x t).V_tok j l) :
    0 < detectorMass T τ Θ₀ x t j := by
  unfold detectorMass
  exact Finset.sum_pos
    (fun l _ => mul_pos (hpos l) (sinkhornDetGain_pos _ _ _)) Finset.univ_nonempty

/-- Normalized detector responsibilities sum to one when calibrated mass is nonzero. -/
theorem detector_responsibilities_sum_one
    (T : ℕ) (τ : ℝ) (Θ₀ : Matrix K K ℝ)
    (x : C → ChunkInput L K D) (t : C) (j : L)
    (hmass : detectorMass T τ Θ₀ x t j ≠ 0) :
    (∑ l, ((x t).V_tok j l *
      sinkhornDetGain T (blockCausalLogScore x τ Θ₀ t) l) /
        detectorMass T τ Θ₀ x t j) = 1 := by
  rw [← Finset.sum_div]
  exact div_self hmass

/-- The normalized companion computes exactly a responsibility-weighted readout. -/
theorem normalizedChunkOutput_eq_responsibility_readout
    (Ψ : Matrix K K ℝ → Matrix K D ℝ → Matrix K D ℝ → Matrix K D ℝ)
    (T : ℕ) (τ : ℝ) (Θ₀ : Matrix K K ℝ)
    (x : C → ChunkInput L K D) (t : C) (j : L) (d : D) :
    normalizedChunkOutput Ψ T τ Θ₀ x t j d =
      ∑ l, (((x t).V_tok j l *
          sinkhornDetGain T (blockCausalLogScore x τ Θ₀ t) l) /
            detectorMass T τ Θ₀ x t j) *
        Ψ (sinkhornMatrix T (blockCausalLogScore x τ Θ₀ t))
          (causalPrefixPool (causalPrefixWeights (fun s => (x s).m_shape))
            (fun s => (x s).V_shape) t) (x t).V_det l d := by
  unfold normalizedChunkOutput blockCausalSinkhornChunkOutput
  dsimp only
  rw [Matrix.mul_apply, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro l _
  ring

/-- Local detector normalization does not introduce a future dependence. -/
theorem normalizedChunkOutput_isBlockCausal
    (Ψ : Matrix K K ℝ → Matrix K D ℝ → Matrix K D ℝ → Matrix K D ℝ)
    (T : ℕ) (τ : ℝ) (Θ₀ : Matrix K K ℝ) :
    IsBlockCausalOperator (fun x t => normalizedChunkOutput Ψ T τ Θ₀ x t) := by
  intro t x₁ x₂ hpast
  have h := blockCausalSinkhorn_zero_future_dependence Ψ T τ Θ₀ x₁ x₂ t hpast
  have ht := hpast t le_rfl
  ext j d
  simp only [normalizedChunkOutput, h.2.2.2.2, detectorMass, h.1, ht]

/-- Direct specialization to the actual normalized chunk pipeline on raw
normed inputs. This closes the gap between the generic derivative result and
the summary structure, for fixed parameters and any fixed local solver. -/
theorem encoded_normalized_future_derivative
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (encode : C → E → ChunkInput L K D)
    (Ψ : Matrix K K ℝ → Matrix K D ℝ → Matrix K D ℝ → Matrix K D ℝ)
    (T : ℕ) (τ : ℝ) (Θ₀ : Matrix K K ℝ)
    (x : C → E) {t s₀ : C} (hts₀ : t < s₀)
    (ℓ : (Matrix L D ℝ) →L[ℝ] ℝ) :
    HasFDerivAt
      (fun v : E => normalizedChunkOutput Ψ T τ Θ₀
        (fun s => encode s ((Function.update x s₀ v) s)) t)
      (0 : E →L[ℝ] Matrix L D ℝ) (x s₀) ∧
    HasFDerivAt
      (fun v : E => ℓ (normalizedChunkOutput Ψ T τ Θ₀
        (fun s => encode s ((Function.update x s₀ v) s)) t))
      (0 : E →L[ℝ] ℝ) (x s₀) ∧
    ℓ.comp (0 : E →L[ℝ] Matrix L D ℝ) = 0 := by
  exact blockCausal_future_hasFDerivAt_zero_and_pullback_zero
    ((normalizedChunkOutput_isBlockCausal Ψ T τ Θ₀).encode encode) x hts₀ ℓ

end
end InfoGeometry.Routing.BlockCausalSinkhorn
