import Mathlib
import InfoGeometry.Topology.SymbolicLatentPathImageTopCat
import InfoGeometry.Topology.SymbolicLatentFeasibleSubspaceTopCat

namespace InfoGeometry.Topology

open CategoryTheory

/-!
# Feasibility factorization of observed path images

Under an explicit staying-feasible hypothesis, an observed path image maps
through the native feasible feature-region subtype.  The resulting
factorization is recorded in `TopCat`; no feasibility hypothesis is hidden in
the definitions.
-/

theorem observedSymbolicLatentPathImage_mem_feasibleFeatureRegion
    {X : Type} [TopologicalSpace X]
    {ι : Type} [Fintype ι]
    (S : FiniteSymbolicLatentSystem X ι)
    (targets : ι → Set ℝ)
    (γ : SymbolicLatentPath X)
    (hγ : ∀ t : SymbolicPathDomain, ∀ i : ι,
      (symbolicObservationPath S γ) t i ∈ targets i)
    (y : observedSymbolicLatentPathImage S γ) :
    y.1 ∈ symbolicLatentFeasibleFeatureRegion targets := by
  have hy : y.1 ∈ symbolicObservationMap S ''
      symbolicLatentPathImage γ := by
    rw [← observedSymbolicLatentPathImage_eq_observation_image S γ]
    exact y.property
  simpa [symbolicLatentFeasibleFeatureRegion] using
    (observedSymbolicLatentPathImage_subset_feasibleSet_of_stays
      S targets γ hγ hy)

def observedSymbolicLatentPathImageToFeasibleRegionTopCatHom
    {X : Type} [TopologicalSpace X]
    {ι : Type} [Fintype ι]
    (S : FiniteSymbolicLatentSystem X ι)
    (targets : ι → Set ℝ)
    (γ : SymbolicLatentPath X)
    (hγ : ∀ t : SymbolicPathDomain, ∀ i : ι,
      (symbolicObservationPath S γ) t i ∈ targets i) :
    TopCat.of (observedSymbolicLatentPathImage S γ) ⟶
      TopCat.of (symbolicLatentFeasibleFeatureRegion targets) :=
  TopCat.ofHom
    { toFun := fun y =>
        ⟨y.1, observedSymbolicLatentPathImage_mem_feasibleFeatureRegion
          S targets γ hγ y⟩
      continuous_toFun := continuous_subtype_val.subtype_mk
        (fun y => observedSymbolicLatentPathImage_mem_feasibleFeatureRegion
          S targets γ hγ y) }

theorem observedSymbolicLatentPathImageToFeasibleRegionTopCatHom_apply
    {X : Type} [TopologicalSpace X]
    {ι : Type} [Fintype ι]
    (S : FiniteSymbolicLatentSystem X ι)
    (targets : ι → Set ℝ)
    (γ : SymbolicLatentPath X)
    (hγ : ∀ t : SymbolicPathDomain, ∀ i : ι,
      (symbolicObservationPath S γ) t i ∈ targets i)
    (y : observedSymbolicLatentPathImage S γ) :
    observedSymbolicLatentPathImageToFeasibleRegionTopCatHom
        S targets γ hγ y =
      ⟨y.1, observedSymbolicLatentPathImage_mem_feasibleFeatureRegion
        S targets γ hγ y⟩ :=
  rfl

noncomputable def observedSymbolicLatentPathImage_compactSpace
    {X : Type} [TopologicalSpace X]
    {ι : Type} [Fintype ι]
    (S : FiniteSymbolicLatentSystem X ι)
    (γ : SymbolicLatentPath X) :
    CompactSpace (observedSymbolicLatentPathImage S γ) :=
  isCompact_iff_compactSpace.mp
    (isCompact_observedSymbolicLatentPathImage S γ)

theorem observedSymbolicLatentPathImageToFeasibleRegion_isClosedEmbedding
    {X : Type} [TopologicalSpace X]
    {ι : Type} [Fintype ι]
    (S : FiniteSymbolicLatentSystem X ι)
    (targets : ι → Set ℝ)
    (γ : SymbolicLatentPath X)
    (hγ : ∀ t : SymbolicPathDomain, ∀ i : ι,
      (symbolicObservationPath S γ) t i ∈ targets i) :
    Topology.IsClosedEmbedding
      (fun y : observedSymbolicLatentPathImage S γ =>
        (⟨y.1, observedSymbolicLatentPathImage_mem_feasibleFeatureRegion
          S targets γ hγ y⟩ :
          symbolicLatentFeasibleFeatureRegion targets)) := by
  letI : CompactSpace (observedSymbolicLatentPathImage S γ) :=
    observedSymbolicLatentPathImage_compactSpace S γ
  apply Continuous.isClosedEmbedding
  · exact continuous_subtype_val.subtype_mk (fun y =>
      observedSymbolicLatentPathImage_mem_feasibleFeatureRegion
        S targets γ hγ y)
  · intro y z h
    exact Subtype.ext (congrArg
      (fun w : symbolicLatentFeasibleFeatureRegion targets => w.1) h)

theorem observedSymbolicLatentPathImageToFeasibleRegion_factorization
    {X : Type} [TopologicalSpace X]
    {ι : Type} [Fintype ι]
    (S : FiniteSymbolicLatentSystem X ι)
    (targets : ι → Set ℝ)
    (γ : SymbolicLatentPath X)
    (hγ : ∀ t : SymbolicPathDomain, ∀ i : ι,
      (symbolicObservationPath S γ) t i ∈ targets i) :
    observedSymbolicLatentPathImageToFeasibleRegionTopCatHom
        S targets γ hγ ≫
        symbolicLatentFeasibleFeatureRegionInclusionTopCatHom targets =
      observedSymbolicLatentPathImageInclusionTopCatHom S γ := by
  ext y
  rfl

theorem observedSymbolicLatentPathImageToFeasibleRegion_unique
    {X : Type} [TopologicalSpace X]
    {ι : Type} [Fintype ι]
    (S : FiniteSymbolicLatentSystem X ι)
    (targets : ι → Set ℝ)
    (γ : SymbolicLatentPath X)
    (hγ : ∀ t : SymbolicPathDomain, ∀ i : ι,
      (symbolicObservationPath S γ) t i ∈ targets i)
    {u : TopCat.of (observedSymbolicLatentPathImage S γ) ⟶
      TopCat.of (symbolicLatentFeasibleFeatureRegion targets)}
    (hu : u ≫ symbolicLatentFeasibleFeatureRegionInclusionTopCatHom targets =
      observedSymbolicLatentPathImageInclusionTopCatHom S γ) :
    u = observedSymbolicLatentPathImageToFeasibleRegionTopCatHom
        S targets γ hγ := by
  apply TopCat.hom_ext
  ext y x
  have hy := congrArg (fun m => m y x) hu
  simpa [observedSymbolicLatentPathImageToFeasibleRegionTopCatHom,
    symbolicLatentFeasibleFeatureRegionInclusionTopCatHom,
    observedSymbolicLatentPathImageInclusionTopCatHom,
    TopCat.comp_app, TopCat.ofHom] using hy

end InfoGeometry.Topology
