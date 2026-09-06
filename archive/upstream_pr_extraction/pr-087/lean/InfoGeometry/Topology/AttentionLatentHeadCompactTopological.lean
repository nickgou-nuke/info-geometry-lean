import InfoGeometry.Topology.AttentionLatentHeadTopological

namespace InfoGeometry.Topology

variable {X n V : Type*}
variable [TopologicalSpace X] [Fintype n] [Nonempty n]
variable [TopologicalSpace V] [AddCommMonoid V] [ContinuousAdd V]
variable [SMul ℝ V] [ContinuousSMul ℝ V]

/-- A continuous finite latent readout has compact range on compact input. -/
theorem isCompact_range_latentAttentionHead
    [CompactSpace X]
    (logits : X → n → ℝ) (values : n → V)
    (hlogits : ∀ i, Continuous (fun x => logits x i)) :
    IsCompact (Set.range (latentAttentionHead logits values)) :=
  isCompact_range (continuous_latentAttentionHead logits values hlogits)

/-- The compact latent readout range is closed in a Hausdorff codomain. -/
theorem isClosed_range_latentAttentionHead
    [CompactSpace X] [T2Space V]
    (logits : X → n → ℝ) (values : n → V)
    (hlogits : ∀ i, Continuous (fun x => logits x i)) :
    IsClosed (Set.range (latentAttentionHead logits values)) :=
  (isCompact_range_latentAttentionHead logits values hlogits).isClosed

/-- Fibers of a continuous latent readout are compact on compact input. -/
theorem isCompact_latentAttentionHead_fiber
    [CompactSpace X] [T1Space V]
    (logits : X → n → ℝ) (values : n → V)
    (hlogits : ∀ i, Continuous (fun x => logits x i)) (v : V) :
    IsCompact {x : X | latentAttentionHead logits values x = v} :=
  IsClosed.isCompact
    (latentAttentionHead_fiber_isClosed logits values hlogits v)

end InfoGeometry.Topology
