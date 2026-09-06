import InfoGeometry.Topology.SymbolicLatentPathImageCompHaus
import Mathlib.Topology.Category.CompHaus.Basic

/-!
# Compact-Hausdorff transport of symbolic-latent path images

The underlying continuous transport already lives in `TopCat`.  Under the
ambient Hausdorff hypotheses, the path images are compact Hausdorff, so the
same map can be packaged as a `CompHaus` morphism.  This owner deliberately
does not impose compactness on the ambient path space.
-/

namespace InfoGeometry.Topology

open CategoryTheory

noncomputable section

def symbolicLatentPathImageMapCompHausHom
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    [T2Space X] [T2Space Y]
    (f : X → Y) (hf : Continuous f) (γ : SymbolicLatentPath X) :
    symbolicLatentPathImageCompHaus γ ⟶
      symbolicLatentPathImageCompHaus
        (mapSymbolicLatentPathContinuous f hf γ) := by
  dsimp [symbolicLatentPathImageCompHaus]
  letI : CompactSpace (symbolicLatentPathImage γ) :=
    isCompact_iff_compactSpace.mp (isCompact_symbolicLatentPathImage γ)
  letI : CompactSpace
      (symbolicLatentPathImage
        (mapSymbolicLatentPathContinuous f hf γ)) :=
    isCompact_iff_compactSpace.mp
      (isCompact_symbolicLatentPathImage
        (mapSymbolicLatentPathContinuous f hf γ))
  exact ⟨symbolicLatentPathImageMapTopCatHom f hf γ⟩

theorem symbolicLatentPathImageMapCompHausHom_forget
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    [T2Space X] [T2Space Y]
    (f : X → Y) (hf : Continuous f) (γ : SymbolicLatentPath X) :
    compHausToTop.map (symbolicLatentPathImageMapCompHausHom f hf γ) =
      symbolicLatentPathImageMapTopCatHom f hf γ := by
  apply TopCat.hom_ext
  ext x
  rfl

@[simp] theorem symbolicLatentPathImageMapCompHausHom_apply
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    [T2Space X] [T2Space Y]
    (f : X → Y) (hf : Continuous f) (γ : SymbolicLatentPath X)
    (x : symbolicLatentPathImage γ) :
    symbolicLatentPathImageMapCompHausHom f hf γ x =
      ⟨f x.1, by
        rw [symbolicLatentPathImage_map_eq_image f hf γ]
        exact ⟨x.1, x.property, rfl⟩⟩ :=
  rfl

theorem symbolicLatentPathImageMapCompHausHom_comp
    {X Y Z : Type} [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace Z]
    [T2Space X] [T2Space Y] [T2Space Z]
    (f : X → Y) (g : Y → Z)
    (hf : Continuous f) (hg : Continuous g)
    (γ : SymbolicLatentPath X) :
    symbolicLatentPathImageMapCompHausHom f hf γ ≫
        symbolicLatentPathImageMapCompHausHom g hg
          (mapSymbolicLatentPathContinuous f hf γ) =
      symbolicLatentPathImageMapCompHausHom (g ∘ f) (hg.comp hf) γ := by
  have hFF : (compHausToTop).FullyFaithful := by
    simpa using (CompHausLike.fullyFaithfulCompHausLikeToTop (fun _ => True))
  apply hFF.map_injective
  rw [Functor.map_comp]
  simpa using
    (symbolicLatentPathImageMapTopCatHom_comp f g hf hg γ)

end
end InfoGeometry.Topology
