import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Topology.SymbolicLatentObservedFamilyImageTopCat
import InfoGeometry.Topology.SymbolicLatentFeasibleSubspaceTopCat

namespace InfoGeometry.Topology

open CategoryTheory

/-!
# Feasibility factorization for the observed symbolic-latent family image

The jointly observed family image already lives as a subtype of the feature
space. Under an explicit pointwise feasibility property, it factors through
the native feasible feature-region subtype.
-/

theorem observedSymbolicLatentPathFamilyImage_mem_feasibleFeatureRegion
    {P X : Type} [TopologicalSpace P] [TopologicalSpace X]
    {ι : Type} [Fintype ι]
    (S : FiniteSymbolicLatentSystem X ι)
    (H : SymbolicLatentPathFamily P X)
    (h_obs : Continuous (symbolicObservationMap S))
    (targets : ι → Set ℝ)
    (hH : ∀ q : P × SymbolicPathDomain, ∀ i : ι,
      symbolicObservationMap S (H q) i ∈ targets i) :
    observedSymbolicLatentPathFamilyImage S H h_obs ⊆
      symbolicLatentFeasibleFeatureRegion targets := by
  intro y hy
  rcases hy with ⟨q, rfl⟩
  intro i
  exact hH q i

def observedSymbolicLatentPathFamilyImageToFeasibleRegionTopCatHom
    {P X : Type} [TopologicalSpace P] [TopologicalSpace X]
    {ι : Type} [Fintype ι]
    (S : FiniteSymbolicLatentSystem X ι)
    (H : SymbolicLatentPathFamily P X)
    (h_obs : Continuous (symbolicObservationMap S))
    (targets : ι → Set ℝ)
    (hH : ∀ q : P × SymbolicPathDomain, ∀ i : ι,
      symbolicObservationMap S (H q) i ∈ targets i) :
    TopCat.of (observedSymbolicLatentPathFamilyImage S H h_obs) ⟶
      TopCat.of (symbolicLatentFeasibleFeatureRegion targets) :=
  TopCat.ofHom
    { toFun := fun y =>
        ⟨y.1,
          observedSymbolicLatentPathFamilyImage_mem_feasibleFeatureRegion
            S H h_obs targets hH y.2⟩
      continuous_toFun :=
        continuous_subtype_val.subtype_mk
          (fun y =>
            observedSymbolicLatentPathFamilyImage_mem_feasibleFeatureRegion
              S H h_obs targets hH y.2) }

theorem observedSymbolicLatentPathFamilyImageToFeasibleRegionTopCatHom_apply
    {P X : Type} [TopologicalSpace P] [TopologicalSpace X]
    {ι : Type} [Fintype ι]
    (S : FiniteSymbolicLatentSystem X ι)
    (H : SymbolicLatentPathFamily P X)
    (h_obs : Continuous (symbolicObservationMap S))
    (targets : ι → Set ℝ)
    (hH : ∀ q : P × SymbolicPathDomain, ∀ i : ι,
      symbolicObservationMap S (H q) i ∈ targets i)
    (y : observedSymbolicLatentPathFamilyImage S H h_obs) :
    observedSymbolicLatentPathFamilyImageToFeasibleRegionTopCatHom
        S H h_obs targets hH y =
      ⟨y.1, observedSymbolicLatentPathFamilyImage_mem_feasibleFeatureRegion
        S H h_obs targets hH y.2⟩ :=
  rfl

theorem observedSymbolicLatentPathFamilyImageToFeasibleRegion_factorization
    {P X : Type} [TopologicalSpace P] [TopologicalSpace X]
    {ι : Type} [Fintype ι]
    (S : FiniteSymbolicLatentSystem X ι)
    (H : SymbolicLatentPathFamily P X)
    (h_obs : Continuous (symbolicObservationMap S))
    (targets : ι → Set ℝ)
    (hH : ∀ q : P × SymbolicPathDomain, ∀ i : ι,
      symbolicObservationMap S (H q) i ∈ targets i) :
    observedSymbolicLatentPathFamilyImageToFeasibleRegionTopCatHom
        S H h_obs targets hH ≫
        symbolicLatentFeasibleFeatureRegionInclusionTopCatHom targets =
      observedSymbolicLatentPathFamilyImageInclusionTopCatHom S H h_obs := by
  ext y
  rfl

theorem observedSymbolicLatentPathFamilyImageToFeasibleRegion_unique
    {P X : Type} [TopologicalSpace P] [TopologicalSpace X]
    {ι : Type} [Fintype ι]
    (S : FiniteSymbolicLatentSystem X ι)
    (H : SymbolicLatentPathFamily P X)
    (h_obs : Continuous (symbolicObservationMap S))
    (targets : ι → Set ℝ)
    (hH : ∀ q : P × SymbolicPathDomain, ∀ i : ι,
      symbolicObservationMap S (H q) i ∈ targets i)
    {u : TopCat.of (observedSymbolicLatentPathFamilyImage S H h_obs) ⟶
      TopCat.of (symbolicLatentFeasibleFeatureRegion targets)}
    (hu : u ≫ symbolicLatentFeasibleFeatureRegionInclusionTopCatHom targets =
      observedSymbolicLatentPathFamilyImageInclusionTopCatHom S H h_obs) :
    u = observedSymbolicLatentPathFamilyImageToFeasibleRegionTopCatHom
        S H h_obs targets hH := by
  apply TopCat.hom_ext
  ext y x
  have hy := congrArg (fun m => m y x) hu
  simpa [observedSymbolicLatentPathFamilyImageToFeasibleRegionTopCatHom,
    symbolicLatentFeasibleFeatureRegionInclusionTopCatHom,
    observedSymbolicLatentPathFamilyImageInclusionTopCatHom,
    TopCat.comp_app, TopCat.ofHom] using hy

end InfoGeometry.Topology
