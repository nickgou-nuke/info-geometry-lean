import InfoGeometry.Topology.TopologicalCovariantFlowMorphism
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Topology.Category.TopCat.Basic

/-!
# The category of fixed-carrier topological covariant flows

The morphism owner fixes the observable carrier `S` and records both the
continuous latent map and the compatible operator automorphism.  This file
packages that already-proved calculus as a genuine category and exposes the
canonical forgetful functor to `TopCat`.
-/

noncomputable section

namespace InfoGeometry.Topology

open CategoryTheory

universe u

variable {X A ι : Type u}
  [TopologicalSpace X] [CompactSpace X]
  [NormedRing A] [StarRing A] [Algebra ℂ A] [Fintype ι]

variable {S : NoncommutativeObservableSystem X A ι}

instance topologicalCovariantFlowCategory :
    Category (NoncommutativeObservableTopologicalCovariantFlow S) where
  Hom F G := TopologicalCovariantFlowMorphism F G
  id F := TopologicalCovariantFlowMorphism.id F
  comp f g := TopologicalCovariantFlowMorphism.comp f g
  id_comp f := TopologicalCovariantFlowMorphism.id_comp f
  comp_id f := TopologicalCovariantFlowMorphism.comp_id f
  assoc f g h := by
    apply TopologicalCovariantFlowMorphism.ext
    · funext x
      rfl
    · ext a
      rfl

noncomputable def latentSpaceForgetfulFunctor :
    NoncommutativeObservableTopologicalCovariantFlow S ⥤ TopCat where
  obj _ := TopCat.of X
  map f := TopCat.ofHom
    { toFun := f.latentMap
      continuous_toFun := f.continuous_latentMap }
  map_id := by
    intro F
    ext x
    rfl
  map_comp f g := by
    ext x
    rfl

@[simp] theorem latentSpaceForgetfulFunctor_obj
    (F : NoncommutativeObservableTopologicalCovariantFlow S) :
    (latentSpaceForgetfulFunctor (S := S)).obj F = TopCat.of X := rfl

@[simp] theorem latentSpaceForgetfulFunctor_map_apply
    {F G : NoncommutativeObservableTopologicalCovariantFlow S}
    (f : F ⟶ G) (x : X) :
    (latentSpaceForgetfulFunctor (S := S)).map f x = f.latentMap x := rfl

end InfoGeometry.Topology
