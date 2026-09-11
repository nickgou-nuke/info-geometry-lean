import InfoGeometry.Topology.SymbolicLatentPathFamilyImageCompHaus
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Topology.SymbolicLatentObservedFamilyImageFeasibleTopCat
import InfoGeometry.Topology.SymbolicLatentFeasibleRegionCompHaus

namespace InfoGeometry.Topology

open CategoryTheory

noncomputable section

/-- Compact-Hausdorff feasible factorization for a jointly observed symbolic
path-family image. -/
noncomputable def observedSymbolicLatentPathFamilyImageToFeasibleRegionCompHausHom
    {P X ι : Type} [TopologicalSpace P] [TopologicalSpace X]
    [CompactSpace P] [Fintype ι]
    (S : FiniteSymbolicLatentSystem X ι)
    (H : SymbolicLatentPathFamily P X)
    (h_obs : Continuous (symbolicObservationMap S))
    (targets : ι → Set ℝ)
    (hH : ∀ q : P × SymbolicPathDomain, ∀ i : ι,
      symbolicObservationMap S (H q) i ∈ targets i)
    (hcompact : ∀ i, IsCompact (targets i)) :
    observedSymbolicLatentPathFamilyImageCompHaus S H h_obs ⟶
      symbolicLatentFeasibleFeatureRegionCompHaus targets hcompact := by
  letI : CompactSpace (observedSymbolicLatentPathFamilyImage S H h_obs) :=
    isCompact_iff_compactSpace.mp
      (isCompact_observedSymbolicLatentPathFamilyImage S H h_obs)
  letI : CompactSpace (symbolicLatentFeasibleFeatureRegion targets) :=
    isCompact_iff_compactSpace.mp
      (isCompact_symbolicLatentFeasibleFeatureRegion targets hcompact)
  dsimp [observedSymbolicLatentPathFamilyImageCompHaus,
    symbolicLatentFeasibleFeatureRegionCompHaus]
  change CompHaus.of (observedSymbolicLatentPathFamilyImage S H h_obs) ⟶
    CompHaus.of (symbolicLatentFeasibleFeatureRegion targets)
  refine ⟨TopCat.ofHom
    { toFun := fun y =>
        ⟨y.1, observedSymbolicLatentPathFamilyImage_mem_feasibleFeatureRegion
          S H h_obs targets hH y.2⟩
      continuous_toFun := continuous_subtype_val.subtype_mk (fun y =>
        observedSymbolicLatentPathFamilyImage_mem_feasibleFeatureRegion
          S H h_obs targets hH y.2) }⟩

theorem observedSymbolicLatentPathFamilyImageToFeasibleRegionCompHausHom_forget
    {P X ι : Type} [TopologicalSpace P] [TopologicalSpace X]
    [CompactSpace P] [Fintype ι]
    (S : FiniteSymbolicLatentSystem X ι)
    (H : SymbolicLatentPathFamily P X)
    (h_obs : Continuous (symbolicObservationMap S))
    (targets : ι → Set ℝ)
    (hH : ∀ q : P × SymbolicPathDomain, ∀ i : ι,
      symbolicObservationMap S (H q) i ∈ targets i)
    (hcompact : ∀ i, IsCompact (targets i)) :
    compHausToTop.map
        (observedSymbolicLatentPathFamilyImageToFeasibleRegionCompHausHom
          S H h_obs targets hH hcompact) =
      observedSymbolicLatentPathFamilyImageToFeasibleRegionTopCatHom
        S H h_obs targets hH := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro y
  rfl

theorem observedSymbolicLatentPathFamilyImageToFeasibleRegionCompHausHom_isClosedEmbedding
    {P X ι : Type} [TopologicalSpace P] [TopologicalSpace X]
    [CompactSpace P] [Fintype ι]
    (S : FiniteSymbolicLatentSystem X ι)
    (H : SymbolicLatentPathFamily P X)
    (h_obs : Continuous (symbolicObservationMap S))
    (targets : ι → Set ℝ)
    (hH : ∀ q : P × SymbolicPathDomain, ∀ i : ι,
      symbolicObservationMap S (H q) i ∈ targets i) :
    Topology.IsClosedEmbedding
      (fun y : observedSymbolicLatentPathFamilyImage S H h_obs =>
        (⟨y.1, observedSymbolicLatentPathFamilyImage_mem_feasibleFeatureRegion
          S H h_obs targets hH y.2⟩ :
          symbolicLatentFeasibleFeatureRegion targets)) := by
  letI : CompactSpace (observedSymbolicLatentPathFamilyImage S H h_obs) :=
    isCompact_iff_compactSpace.mp
      (isCompact_observedSymbolicLatentPathFamilyImage S H h_obs)
  apply Continuous.isClosedEmbedding
  · exact continuous_subtype_val.subtype_mk (fun y =>
      observedSymbolicLatentPathFamilyImage_mem_feasibleFeatureRegion
        S H h_obs targets hH y.2)
  · intro y z h
    exact Subtype.ext (congrArg
      (fun w : symbolicLatentFeasibleFeatureRegion targets => w.1) h)

end

end InfoGeometry.Topology
