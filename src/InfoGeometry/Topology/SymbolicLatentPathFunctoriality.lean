import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Topology.SymbolicLatentPathEndpoints

open CategoryTheory

namespace InfoGeometry.Topology

/-!
# Functoriality of symbolic latent paths

This is the generic topological transport layer.  Chart morphisms are a
specialized instance, while this owner works for every continuous map.
-/

def mapSymbolicLatentPathContinuous
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Y) (hf : Continuous f)
    (γ : SymbolicLatentPath X) : SymbolicLatentPath Y :=
  { toFun := fun t => f (γ t)
    continuous_toFun := hf.comp γ.continuous }

@[simp] theorem mapSymbolicLatentPathContinuous_apply
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Y) (hf : Continuous f)
    (γ : SymbolicLatentPath X) (t : SymbolicPathDomain) :
    mapSymbolicLatentPathContinuous f hf γ t = f (γ t) := rfl

theorem mapSymbolicLatentPathContinuous_start
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Y) (hf : Continuous f)
    (γ : SymbolicLatentPath X) :
    (mapSymbolicLatentPathContinuous f hf γ).start = f γ.start := rfl

theorem mapSymbolicLatentPathContinuous_finish
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Y) (hf : Continuous f)
    (γ : SymbolicLatentPath X) :
    (mapSymbolicLatentPathContinuous f hf γ).finish = f γ.finish := rfl

theorem mapSymbolicLatentPathContinuous_id
    {X : Type*} [TopologicalSpace X]
    (γ : SymbolicLatentPath X) :
    mapSymbolicLatentPathContinuous id continuous_id γ = γ := by
  ext t
  rfl

theorem mapSymbolicLatentPathContinuous_comp
    {X Y Z : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    (f : X → Y) (g : Y → Z)
    (hf : Continuous f) (hg : Continuous g)
    (γ : SymbolicLatentPath X) :
    mapSymbolicLatentPathContinuous g hg
      (mapSymbolicLatentPathContinuous f hf γ) =
      mapSymbolicLatentPathContinuous (g ∘ f) (hg.comp hf) γ := by
  ext t
  rfl

def symbolicLatentPathTopCatHom
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Y) (hf : Continuous f) :
    TopCat.of (C(SymbolicPathDomain, X)) ⟶
      TopCat.of (C(SymbolicPathDomain, Y)) :=
  let F : C(X, Y) := ⟨f, hf⟩
  TopCat.ofHom
    { toFun := F.comp
      continuous_toFun := by
        simpa [mapSymbolicLatentPathContinuous] using
          (ContinuousMap.continuous_postcomp F) }

theorem symbolicLatentPathTopCatHom_apply
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Y) (hf : Continuous f)
    (γ : SymbolicLatentPath X) :
    symbolicLatentPathTopCatHom f hf γ =
      mapSymbolicLatentPathContinuous f hf γ :=
  rfl

theorem symbolicLatentPathTopCatHom_id
    {X : Type} [TopologicalSpace X] :
    symbolicLatentPathTopCatHom (fun x : X => x) continuous_id =
      𝟙 (TopCat.of (SymbolicLatentPath X)) := by
  ext γ t
  rfl

theorem symbolicLatentPathTopCatHom_comp
    {X Y Z : Type}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    (f : X → Y) (g : Y → Z)
    (hf : Continuous f) (hg : Continuous g) :
    symbolicLatentPathTopCatHom f hf ≫
        symbolicLatentPathTopCatHom g hg =
      symbolicLatentPathTopCatHom (g ∘ f) (hg.comp hf) := by
  ext γ t
  rfl

theorem symbolicLatentPathTopCatHom_comp_apply
    {X Y Z : Type}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    (f : X → Y) (g : Y → Z)
    (hf : Continuous f) (hg : Continuous g)
    (γ : SymbolicLatentPath X) (t : SymbolicPathDomain) :
    (symbolicLatentPathTopCatHom f hf ≫
        symbolicLatentPathTopCatHom g hg) γ t =
      symbolicLatentPathTopCatHom (g ∘ f) (hg.comp hf) γ t := by
  rfl

end InfoGeometry.Topology
