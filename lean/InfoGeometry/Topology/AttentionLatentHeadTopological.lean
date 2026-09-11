import Mathlib.Topology.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Topology.AttentionLatentSimplexTopological

open scoped BigOperators

namespace InfoGeometry.Topology

variable {X n V : Type*}
variable [TopologicalSpace X] [Fintype n] [Nonempty n]
variable [TopologicalSpace V] [AddCommMonoid V] [ContinuousAdd V]
variable [SMul ℝ V] [ContinuousSMul ℝ V]

/-- The finite Gibbs-weighted value readout of a symbolic latent field. -/
noncomputable def latentAttentionHead (logits : X → n → ℝ) (values : n → V) : X → V :=
  fun x => ∑ i : n, latentSoftmax logits x i • values i

theorem continuous_latentAttentionHead
    (logits : X → n → ℝ) (values : n → V)
    (hlogits : ∀ i, Continuous (fun x => logits x i)) :
    Continuous (latentAttentionHead logits values) := by
  unfold latentAttentionHead
  apply continuous_finset_sum (s := (Finset.univ : Finset n))
  intro i hi
  exact (continuous_latentSoftmax_coordinate logits hlogits i).smul
    continuous_const

theorem latentAttentionHead_fiber_isClosed
    [T1Space V]
    (logits : X → n → ℝ) (values : n → V)
    (hlogits : ∀ i, Continuous (fun x => logits x i))
    (v : V) :
    IsClosed {x : X | latentAttentionHead logits values x = v} := by
  change IsClosed ((latentAttentionHead logits values) ⁻¹' ({v} : Set V))
  exact isClosed_singleton.preimage
    (continuous_latentAttentionHead logits values hlogits)

theorem latentAttentionHead_readout_continuous_simplex
    (logits : X → n → ℝ) (values : n → V)
    (hlogits : ∀ i, Continuous (fun x => logits x i)) :
    Continuous (latentAttentionHead logits values) ∧
      (∀ x, ∑ i : n, latentSoftmax logits x i = 1) ∧
      (∀ x i, 0 ≤ latentSoftmax logits x i) := by
  exact ⟨continuous_latentAttentionHead logits values hlogits,
    fun x => latentSoftmax_sum_one logits x,
    fun x i => latentSoftmax_nonneg logits x i⟩

end InfoGeometry.Topology
