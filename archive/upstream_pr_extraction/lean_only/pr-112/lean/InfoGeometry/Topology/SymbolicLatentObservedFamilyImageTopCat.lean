import Mathlib
import InfoGeometry.Topology.SymbolicLatentObservedFamily
import InfoGeometry.Topology.SymbolicLatentObservedFamilyTopCat

namespace InfoGeometry.Topology

open CategoryTheory

/-!
# `TopCat` factorization through the observed symbolic-latent family image

The jointly observed family already has a native image as a subtype of the
feature space. This file packages the evaluation map into that image, its
inclusion into the ambient feature space, and the factorization through the
image inclusion as `TopCat` morphisms.
-/

def observedSymbolicLatentPathFamilyImageEvaluationTopCatHom
    {P X : Type} [TopologicalSpace P] [TopologicalSpace X]
    {ι : Type} [Fintype ι]
    (S : FiniteSymbolicLatentSystem X ι)
    (H : SymbolicLatentPathFamily P X)
    (h_obs : Continuous (symbolicObservationMap S)) :
    TopCat.of (P × SymbolicPathDomain) ⟶
      TopCat.of (observedSymbolicLatentPathFamilyImage S H h_obs) :=
  TopCat.ofHom
    { toFun := fun q =>
        ⟨observedSymbolicLatentPathFamily S H h_obs q, ⟨q, rfl⟩⟩
      continuous_toFun :=
        (observedSymbolicLatentPathFamily S H h_obs).continuous.subtype_mk
          (fun q => ⟨q, rfl⟩) }

def observedSymbolicLatentPathFamilyImageInclusionTopCatHom
    {P X : Type} [TopologicalSpace P] [TopologicalSpace X]
    {ι : Type} [Fintype ι]
    (S : FiniteSymbolicLatentSystem X ι)
    (H : SymbolicLatentPathFamily P X)
    (h_obs : Continuous (symbolicObservationMap S)) :
    TopCat.of (observedSymbolicLatentPathFamilyImage S H h_obs) ⟶
      TopCat.of (SymbolicFeatureSpace ι) :=
  TopCat.ofHom
    { toFun := Subtype.val
      continuous_toFun := continuous_subtype_val }

theorem observedSymbolicLatentPathFamilyImage_evaluation_factorization
    {P X : Type} [TopologicalSpace P] [TopologicalSpace X]
    {ι : Type} [Fintype ι]
    (S : FiniteSymbolicLatentSystem X ι)
    (H : SymbolicLatentPathFamily P X)
    (h_obs : Continuous (symbolicObservationMap S)) :
    observedSymbolicLatentPathFamilyImageEvaluationTopCatHom S H h_obs ≫
        observedSymbolicLatentPathFamilyImageInclusionTopCatHom S H h_obs =
      observedSymbolicLatentPathFamilyTopCatHom S H h_obs := by
  ext q
  rfl

theorem observedSymbolicLatentPathFamilyImage_evaluation_factorization_unique
    {P X : Type} [TopologicalSpace P] [TopologicalSpace X]
    {ι : Type} [Fintype ι]
    (S : FiniteSymbolicLatentSystem X ι)
    (H : SymbolicLatentPathFamily P X)
    (h_obs : Continuous (symbolicObservationMap S))
    {u : TopCat.of (P × SymbolicPathDomain) ⟶
      TopCat.of (observedSymbolicLatentPathFamilyImage S H h_obs)}
    (hu : u ≫ observedSymbolicLatentPathFamilyImageInclusionTopCatHom S H h_obs =
      observedSymbolicLatentPathFamilyTopCatHom S H h_obs) :
    u = observedSymbolicLatentPathFamilyImageEvaluationTopCatHom S H h_obs := by
  apply TopCat.hom_ext
  ext q x
  have hq := congrArg (fun m => m q x) hu
  simpa [observedSymbolicLatentPathFamilyImageEvaluationTopCatHom,
    observedSymbolicLatentPathFamilyImageInclusionTopCatHom,
    TopCat.comp_app, TopCat.ofHom] using hq

end InfoGeometry.Topology
