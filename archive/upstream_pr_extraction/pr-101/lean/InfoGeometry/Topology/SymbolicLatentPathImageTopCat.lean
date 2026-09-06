import Mathlib
import InfoGeometry.Topology.SymbolicLatentPathImageTransport

namespace InfoGeometry.Topology

open CategoryTheory

/-!
# `TopCat` factorization through symbolic-latent path images

The path image is a native subtype of the ambient latent space.  This owner
records the evaluation map into that subtype, its inclusion into the ambient
space, and the corresponding factorization.  The same construction is
provided for observed paths.
-/

def symbolicLatentPathImageEvaluationTopCatHom
    {X : Type} [TopologicalSpace X]
    (γ : SymbolicLatentPath X) :
    TopCat.of SymbolicPathDomain ⟶
      TopCat.of (symbolicLatentPathImage γ) :=
  TopCat.ofHom
    { toFun := fun t => ⟨γ t, ⟨t, rfl⟩⟩
      continuous_toFun := γ.continuous.subtype_mk (fun t => ⟨t, rfl⟩) }

def symbolicLatentPathImageInclusionTopCatHom
    {X : Type} [TopologicalSpace X]
    (γ : SymbolicLatentPath X) :
    TopCat.of (symbolicLatentPathImage γ) ⟶ TopCat.of X :=
  TopCat.ofHom
    { toFun := Subtype.val
      continuous_toFun := continuous_subtype_val }

def symbolicLatentPathImageAmbientEvaluationTopCatHom
    {X : Type} [TopologicalSpace X]
    (γ : SymbolicLatentPath X) :
    TopCat.of SymbolicPathDomain ⟶ TopCat.of X :=
  TopCat.ofHom
    { toFun := γ
      continuous_toFun := γ.continuous }

theorem symbolicLatentPathImage_evaluation_factorization
    {X : Type} [TopologicalSpace X]
    (γ : SymbolicLatentPath X) :
    symbolicLatentPathImageEvaluationTopCatHom γ ≫
        symbolicLatentPathImageInclusionTopCatHom γ =
      symbolicLatentPathImageAmbientEvaluationTopCatHom γ := by
  ext t
  rfl

theorem symbolicLatentPathImage_evaluation_factorization_unique
    {X : Type} [TopologicalSpace X]
    (γ : SymbolicLatentPath X)
    {u : TopCat.of SymbolicPathDomain ⟶
      TopCat.of (symbolicLatentPathImage γ)}
    (hu : u ≫ symbolicLatentPathImageInclusionTopCatHom γ =
      TopCat.ofHom γ) :
    u = symbolicLatentPathImageEvaluationTopCatHom γ := by
  apply TopCat.hom_ext
  ext t
  have ht := congrArg (fun m => m t) hu
  simpa [symbolicLatentPathImageEvaluationTopCatHom,
    symbolicLatentPathImageInclusionTopCatHom,
    TopCat.comp_app, TopCat.ofHom] using ht

def observedSymbolicLatentPathImageEvaluationTopCatHom
    {X : Type} [TopologicalSpace X]
    {ι : Type} [Fintype ι]
    (S : FiniteSymbolicLatentSystem X ι)
    (γ : SymbolicLatentPath X) :
    TopCat.of SymbolicPathDomain ⟶
      TopCat.of (observedSymbolicLatentPathImage S γ) :=
  TopCat.ofHom
    { toFun := fun t => ⟨symbolicObservationPath S γ t, ⟨t, rfl⟩⟩
      continuous_toFun :=
        (symbolicObservationPath S γ).continuous.subtype_mk (fun t => ⟨t, rfl⟩) }

def observedSymbolicLatentPathImageInclusionTopCatHom
    {X : Type} [TopologicalSpace X]
    {ι : Type} [Fintype ι]
    (S : FiniteSymbolicLatentSystem X ι)
    (γ : SymbolicLatentPath X) :
    TopCat.of (observedSymbolicLatentPathImage S γ) ⟶
      TopCat.of (SymbolicFeatureSpace ι) :=
  TopCat.ofHom
    { toFun := Subtype.val
      continuous_toFun := continuous_subtype_val }

def observedSymbolicLatentPathImageAmbientEvaluationTopCatHom
    {X : Type} [TopologicalSpace X]
    {ι : Type} [Fintype ι]
    (S : FiniteSymbolicLatentSystem X ι)
    (γ : SymbolicLatentPath X) :
    TopCat.of SymbolicPathDomain ⟶
      TopCat.of (SymbolicFeatureSpace ι) :=
  TopCat.ofHom
    { toFun := symbolicObservationPath S γ
      continuous_toFun := (symbolicObservationPath S γ).continuous }

theorem observedSymbolicLatentPathImage_evaluation_factorization
    {X : Type} [TopologicalSpace X]
    {ι : Type} [Fintype ι]
    (S : FiniteSymbolicLatentSystem X ι)
    (γ : SymbolicLatentPath X) :
    observedSymbolicLatentPathImageEvaluationTopCatHom S γ ≫
        observedSymbolicLatentPathImageInclusionTopCatHom S γ =
      observedSymbolicLatentPathImageAmbientEvaluationTopCatHom S γ := by
  ext t
  rfl

theorem observedSymbolicLatentPathImage_evaluation_factorization_unique
    {X : Type} [TopologicalSpace X]
    {ι : Type} [Fintype ι]
    (S : FiniteSymbolicLatentSystem X ι)
    (γ : SymbolicLatentPath X)
    {u : TopCat.of SymbolicPathDomain ⟶
      TopCat.of (observedSymbolicLatentPathImage S γ)}
    (hu : u ≫ observedSymbolicLatentPathImageInclusionTopCatHom S γ =
      observedSymbolicLatentPathImageAmbientEvaluationTopCatHom S γ) :
    u = observedSymbolicLatentPathImageEvaluationTopCatHom S γ := by
  apply TopCat.hom_ext
  ext t x
  have ht := congrArg (fun m => m t x) hu
  simpa [observedSymbolicLatentPathImageEvaluationTopCatHom,
    observedSymbolicLatentPathImageInclusionTopCatHom,
    TopCat.comp_app, TopCat.ofHom] using ht

end InfoGeometry.Topology
