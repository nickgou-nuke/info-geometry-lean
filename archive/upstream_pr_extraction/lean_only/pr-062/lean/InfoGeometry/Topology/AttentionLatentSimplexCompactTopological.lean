import InfoGeometry.Topology.AttentionLatentSimplexTopological

namespace InfoGeometry.Topology

variable {X n : Type*} [TopologicalSpace X] [Fintype n] [Nonempty n]

/-- A point fiber of the normalized symbolic latent map is compact when the
input space is compact. -/
theorem isCompact_latentSimplexMap_fiber
    [CompactSpace X]
    (logits : X → n → ℝ)
    (hlogits : ∀ i, Continuous (fun x => logits x i))
    (p : stdSimplex ℝ n) :
    IsCompact {x : X | latentSimplexMap logits x = p} := by
  apply IsClosed.isCompact
  change IsClosed
    ((latentSimplexMap logits) ⁻¹' ({p} : Set (stdSimplex ℝ n)))
  exact isClosed_singleton.preimage
    (continuous_latentSimplexMap logits hlogits)

/-- A fixed softmax coordinate has compact fibers on compact input. -/
theorem isCompact_latentSoftmax_coordinate_fiber
    [CompactSpace X]
    (logits : X → n → ℝ)
    (hlogits : ∀ i, Continuous (fun x => logits x i))
    (i : n) (c : ℝ) :
    IsCompact {x : X | latentSoftmax logits x i = c} :=
  IsClosed.isCompact
    (latentSoftmax_coordinate_fiber_isClosed logits hlogits i c)

theorem latentSoftmax_coordinate_sublevel_isClosed
    (logits : X → n → ℝ)
    (hlogits : ∀ i, Continuous (fun x => logits x i))
    (i : n) (c : ℝ) :
    IsClosed {x : X | latentSoftmax logits x i ≤ c} := by
  change IsClosed ((fun x => latentSoftmax logits x i) ⁻¹' Set.Iic c)
  exact isClosed_Iic.preimage
    (continuous_latentSoftmax_coordinate logits hlogits i)

theorem latentSoftmax_coordinate_superlevel_isClosed
    (logits : X → n → ℝ)
    (hlogits : ∀ i, Continuous (fun x => logits x i))
    (i : n) (c : ℝ) :
    IsClosed {x : X | c ≤ latentSoftmax logits x i} := by
  change IsClosed ((fun x => latentSoftmax logits x i) ⁻¹' Set.Ici c)
  exact isClosed_Ici.preimage
    (continuous_latentSoftmax_coordinate logits hlogits i)

theorem isCompact_latentSoftmax_coordinate_sublevel
    [CompactSpace X]
    (logits : X → n → ℝ)
    (hlogits : ∀ i, Continuous (fun x => logits x i))
    (i : n) (c : ℝ) :
    IsCompact {x : X | latentSoftmax logits x i ≤ c} :=
  IsClosed.isCompact
    (latentSoftmax_coordinate_sublevel_isClosed logits hlogits i c)

theorem isCompact_latentSoftmax_coordinate_superlevel
    [CompactSpace X]
    (logits : X → n → ℝ)
    (hlogits : ∀ i, Continuous (fun x => logits x i))
    (i : n) (c : ℝ) :
    IsCompact {x : X | c ≤ latentSoftmax logits x i} :=
  IsClosed.isCompact
    (latentSoftmax_coordinate_superlevel_isClosed logits hlogits i c)

end InfoGeometry.Topology
