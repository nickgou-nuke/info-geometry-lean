import InfoGeometry.Topology.SymbolicLatentPathImageFeasibleTopCat
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Topology.SymbolicLatentFeasibleRegionCompHaus

namespace InfoGeometry.Topology

open CategoryTheory

noncomputable section

/-- Compact-Hausdorff packaging of the image of one observed symbolic-latent
path.  Compactness is inherited from the native path-image theorem. -/
noncomputable def observedSymbolicLatentPathImageCompHaus
    {X : Type} [TopologicalSpace X]
    {ι : Type} [Fintype ι]
    (S : FiniteSymbolicLatentSystem X ι)
    (γ : SymbolicLatentPath X) : CompHaus := by
  letI : CompactSpace (observedSymbolicLatentPathImage S γ) :=
    observedSymbolicLatentPathImage_compactSpace S γ
  exact CompHaus.of (observedSymbolicLatentPathImage S γ)

/-- The feasible factorization of an observed path image as a `CompHaus`
morphism.  The compactness of the target region is explicit in the API. -/
noncomputable def observedSymbolicLatentPathImageToFeasibleRegionCompHausHom
    {X : Type} [TopologicalSpace X]
    {ι : Type} [Fintype ι]
    (S : FiniteSymbolicLatentSystem X ι)
    (targets : ι → Set ℝ)
    (γ : SymbolicLatentPath X)
    (hγ : ∀ t : SymbolicPathDomain, ∀ i : ι,
      (symbolicObservationPath S γ) t i ∈ targets i)
    (hcompact : ∀ i, IsCompact (targets i)) :
    observedSymbolicLatentPathImageCompHaus S γ ⟶
      symbolicLatentFeasibleFeatureRegionCompHaus targets hcompact := by
  letI : CompactSpace (observedSymbolicLatentPathImage S γ) :=
    observedSymbolicLatentPathImage_compactSpace S γ
  letI : CompactSpace (symbolicLatentFeasibleFeatureRegion targets) :=
    isCompact_iff_compactSpace.mp
      (isCompact_symbolicLatentFeasibleFeatureRegion targets hcompact)
  dsimp [observedSymbolicLatentPathImageCompHaus,
    symbolicLatentFeasibleFeatureRegionCompHaus]
  change CompHaus.of (observedSymbolicLatentPathImage S γ) ⟶
    CompHaus.of (symbolicLatentFeasibleFeatureRegion targets)
  refine ⟨TopCat.ofHom
    { toFun := fun y =>
        ⟨y.1, observedSymbolicLatentPathImage_mem_feasibleFeatureRegion
          S targets γ hγ y⟩
      continuous_toFun := continuous_subtype_val.subtype_mk (fun y =>
        observedSymbolicLatentPathImage_mem_feasibleFeatureRegion
          S targets γ hγ y) }⟩

theorem observedSymbolicLatentPathImageToFeasibleRegionCompHausHom_forget
    {X : Type} [TopologicalSpace X]
    {ι : Type} [Fintype ι]
    (S : FiniteSymbolicLatentSystem X ι)
    (targets : ι → Set ℝ)
    (γ : SymbolicLatentPath X)
    (hγ : ∀ t : SymbolicPathDomain, ∀ i : ι,
      (symbolicObservationPath S γ) t i ∈ targets i)
    (hcompact : ∀ i, IsCompact (targets i)) :
    compHausToTop.map
        (observedSymbolicLatentPathImageToFeasibleRegionCompHausHom
          S targets γ hγ hcompact) =
      observedSymbolicLatentPathImageToFeasibleRegionTopCatHom
        S targets γ hγ := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro y
  rfl

theorem observedSymbolicLatentPathImageToFeasibleRegionCompHausHom_isClosedEmbedding
    {X : Type} [TopologicalSpace X]
    {ι : Type} [Fintype ι]
    (S : FiniteSymbolicLatentSystem X ι)
    (targets : ι → Set ℝ)
    (γ : SymbolicLatentPath X)
    (hγ : ∀ t : SymbolicPathDomain, ∀ i : ι,
      (symbolicObservationPath S γ) t i ∈ targets i)
    (hcompact : ∀ i, IsCompact (targets i)) :
    Topology.IsClosedEmbedding
      (fun y : observedSymbolicLatentPathImage S γ =>
        (⟨y.1, observedSymbolicLatentPathImage_mem_feasibleFeatureRegion
          S targets γ hγ y⟩ : symbolicLatentFeasibleFeatureRegion targets)) := by
  exact observedSymbolicLatentPathImageToFeasibleRegion_isClosedEmbedding
    S targets γ hγ

end

end InfoGeometry.Topology
