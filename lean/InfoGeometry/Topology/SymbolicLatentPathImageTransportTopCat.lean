import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Topology.SymbolicLatentPathImageTopCat
import InfoGeometry.Topology.SymbolicLatentPathImageTransport

namespace InfoGeometry.Topology

open CategoryTheory

/-!
# `TopCat` transport of symbolic-latent path images

The set-level image identity is already owned by
`symbolicLatentPathImage_map_eq_image`.  This file packages the induced map
between the corresponding native image subtypes.
-/

def symbolicLatentPathImageMapTopCatHom
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Y) (hf : Continuous f) (γ : SymbolicLatentPath X) :
    TopCat.of (symbolicLatentPathImage γ) ⟶
      TopCat.of (symbolicLatentPathImage
        (mapSymbolicLatentPathContinuous f hf γ)) :=
  TopCat.ofHom
    { toFun := fun x =>
        ⟨f x.1, by
          rw [symbolicLatentPathImage_map_eq_image f hf γ]
          exact ⟨x.1, x.property, rfl⟩⟩
      continuous_toFun :=
        (hf.comp continuous_subtype_val).subtype_mk (fun x => by
          rw [symbolicLatentPathImage_map_eq_image f hf γ]
          exact ⟨x.1, x.property, rfl⟩) }

@[simp] theorem symbolicLatentPathImageMapTopCatHom_apply
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Y) (hf : Continuous f) (γ : SymbolicLatentPath X)
    (x : symbolicLatentPathImage γ) :
    symbolicLatentPathImageMapTopCatHom f hf γ x =
      ⟨f x.1, by
        rw [symbolicLatentPathImage_map_eq_image f hf γ]
        exact ⟨x.1, x.property, rfl⟩⟩ :=
  rfl

def continuousMapTopCatHom
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Y) (hf : Continuous f) :
    TopCat.of X ⟶ TopCat.of Y :=
  TopCat.ofHom { toFun := f, continuous_toFun := hf }

theorem symbolicLatentPathImageMapTopCatHom_factorization
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Y) (hf : Continuous f) (γ : SymbolicLatentPath X) :
    symbolicLatentPathImageMapTopCatHom f hf γ ≫
        symbolicLatentPathImageInclusionTopCatHom
          (mapSymbolicLatentPathContinuous f hf γ) =
      symbolicLatentPathImageInclusionTopCatHom γ ≫
        continuousMapTopCatHom f hf := by
  ext x
  rfl

theorem symbolicLatentPathImageMapTopCatHom_factorization_unique
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Y) (hf : Continuous f) (γ : SymbolicLatentPath X)
    {u : TopCat.of (symbolicLatentPathImage γ) ⟶
      TopCat.of (symbolicLatentPathImage
        (mapSymbolicLatentPathContinuous f hf γ))}
    (hu : u ≫
        symbolicLatentPathImageInclusionTopCatHom
          (mapSymbolicLatentPathContinuous f hf γ) =
      symbolicLatentPathImageInclusionTopCatHom γ ≫
        continuousMapTopCatHom f hf) :
    u = symbolicLatentPathImageMapTopCatHom f hf γ := by
  apply TopCat.hom_ext
  ext x
  have hx := congrArg (fun m => m x) hu
  simpa [symbolicLatentPathImageMapTopCatHom,
    symbolicLatentPathImageInclusionTopCatHom,
    continuousMapTopCatHom, TopCat.comp_app, TopCat.ofHom] using hx

theorem symbolicLatentPathImageMapTopCatHom_comp
    {X Y Z : Type} [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace Z]
    (f : X → Y) (g : Y → Z)
    (hf : Continuous f) (hg : Continuous g)
    (γ : SymbolicLatentPath X) :
    symbolicLatentPathImageMapTopCatHom f hf γ ≫
        symbolicLatentPathImageMapTopCatHom g hg
          (mapSymbolicLatentPathContinuous f hf γ) =
      symbolicLatentPathImageMapTopCatHom (g ∘ f) (hg.comp hf) γ := by
  ext x
  rfl

theorem symbolicLatentPathImageMapTopCatHom_comp_apply
    {X Y Z : Type} [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace Z]
    (f : X → Y) (g : Y → Z)
    (hf : Continuous f) (hg : Continuous g)
    (γ : SymbolicLatentPath X)
    (x : symbolicLatentPathImage γ) :
    (symbolicLatentPathImageMapTopCatHom f hf γ ≫
        symbolicLatentPathImageMapTopCatHom g hg
          (mapSymbolicLatentPathContinuous f hf γ)) x =
      symbolicLatentPathImageMapTopCatHom (g ∘ f) (hg.comp hf) γ x := by
  rfl

end InfoGeometry.Topology
