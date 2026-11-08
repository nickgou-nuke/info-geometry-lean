import InfoGeometry.Topology.TopologicalCovariantFlowCategory
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Topology.Category.CompHaus.Basic

/-!
# Compact-Hausdorff forgetful functor for fixed-carrier flows

This is the compact-Hausdorff refinement of the `TopCat` latent-space
forgetful functor.  The observable carrier is fixed, so every flow object is
sent to the same `CompHaus.of X`; morphisms retain only their continuous
latent maps.
-/

noncomputable section

namespace InfoGeometry.Topology

open CategoryTheory

universe u

variable {X A ι : Type u}
  [TopologicalSpace X] [CompactSpace X] [T2Space X]
  [NormedRing A] [StarRing A] [Algebra ℂ A] [Fintype ι]

variable {S : NoncommutativeObservableSystem X A ι}

noncomputable def latentSpaceForgetfulCompHausHom
    {F G : NoncommutativeObservableTopologicalCovariantFlow S}
    (f : F ⟶ G) : CompHaus.of X ⟶ CompHaus.of X :=
  ⟨TopCat.ofHom
    { toFun := f.latentMap
      continuous_toFun := f.continuous_latentMap }⟩

noncomputable def latentSpaceForgetfulCompHausFunctor :
    NoncommutativeObservableTopologicalCovariantFlow S ⥤ CompHaus where
  obj _ := CompHaus.of X
  map f := latentSpaceForgetfulCompHausHom f
  map_id := by
    intro F
    dsimp [latentSpaceForgetfulCompHausHom,
      topologicalCovariantFlowCategory,
      TopologicalCovariantFlowMorphism.id]
    apply (compHausToTop).map_injective
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro x
    rfl
  map_comp f g := by
    dsimp [latentSpaceForgetfulCompHausHom,
      topologicalCovariantFlowCategory,
      TopologicalCovariantFlowMorphism.comp]
    apply (compHausToTop).map_injective
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro x
    rfl

@[simp] theorem latentSpaceForgetfulCompHausFunctor_obj
    (F : NoncommutativeObservableTopologicalCovariantFlow S) :
    (latentSpaceForgetfulCompHausFunctor (S := S)).obj F = CompHaus.of X := rfl

@[simp] theorem latentSpaceForgetfulCompHausFunctor_map_apply
    {F G : NoncommutativeObservableTopologicalCovariantFlow S}
    (f : F ⟶ G) (x : X) :
    (latentSpaceForgetfulCompHausFunctor (S := S)).map f x = f.latentMap x := rfl

theorem latentSpaceForgetfulCompHausFunctor_forget
    {F G : NoncommutativeObservableTopologicalCovariantFlow S}
    (f : F ⟶ G) :
    compHausToTop.map
        ((latentSpaceForgetfulCompHausFunctor (S := S)).map f) =
      (latentSpaceForgetfulFunctor (S := S)).map f := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro x
  rfl

end InfoGeometry.Topology
