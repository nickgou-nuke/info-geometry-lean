import InfoGeometry.Topology.AttentionLatentSimplexCompactTopological

namespace InfoGeometry.Topology

variable {X n : Type*} [TopologicalSpace X] [Fintype n] [Nonempty n]

/-- The strict-positive interior of the standard simplex. -/
def latentSimplexInterior : Set (stdSimplex ℝ n) :=
  {p | ∀ i, 0 < (p : n → ℝ) i}

omit [Nonempty n] in
theorem isOpen_latentSimplexInterior :
    IsOpen (latentSimplexInterior (n := n)) := by
  have hset : latentSimplexInterior (n := n) =
      ⋂ i : n, {p : stdSimplex ℝ n | 0 < (p : n → ℝ) i} := by
    ext p
    simp [latentSimplexInterior]
  rw [hset]
  apply isOpen_iInter_of_finite
  intro i
  exact isOpen_Ioi.preimage
    ((continuous_apply i).comp continuous_subtype_val)

theorem latentSimplexMap_mem_interior
    (logits : X → n → ℝ)
    (_hlogits : ∀ i, Continuous (fun x => logits x i))
    (x : X) :
    latentSimplexMap logits x ∈ latentSimplexInterior (n := n) := by
  intro i
  exact latentSimplexMap_coordinate_pos logits x i

theorem range_latentSimplexMap_subset_interior
    (logits : X → n → ℝ)
    (hlogits : ∀ i, Continuous (fun x => logits x i)) :
    Set.range (latentSimplexMap logits) ⊆ latentSimplexInterior (n := n) := by
  rintro p ⟨x, rfl⟩
  exact latentSimplexMap_mem_interior logits hlogits x

theorem isCompact_range_latentSimplexMap_interior
    [CompactSpace X]
    (logits : X → n → ℝ)
    (hlogits : ∀ i, Continuous (fun x => logits x i)) :
    IsCompact (Set.range (latentSimplexMap logits)) ∧
      Set.range (latentSimplexMap logits) ⊆ latentSimplexInterior (n := n) :=
  ⟨isCompact_range_latentSimplexMap logits hlogits,
    range_latentSimplexMap_subset_interior logits hlogits⟩

end InfoGeometry.Topology
