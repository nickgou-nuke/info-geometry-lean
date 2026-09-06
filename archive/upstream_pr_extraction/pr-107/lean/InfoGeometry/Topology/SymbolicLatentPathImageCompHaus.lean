import InfoGeometry.Topology.SymbolicLatentPathImageTransportHomeomorphTopCat
import Mathlib.Topology.Category.CompHaus.Basic

/-!
# Compact-Hausdorff packaging of symbolic path images

Every symbolic path image is compact.  This owner packages that native
compactness as a `CompHaus` object when the ambient carrier is Hausdorff and
transports it along ambient homeomorphisms.
-/

namespace InfoGeometry.Topology

open CategoryTheory

noncomputable section

noncomputable def symbolicLatentPathImageCompHaus
    {X : Type*} [TopologicalSpace X] [T2Space X]
    (γ : SymbolicLatentPath X) : CompHaus := by
  letI : CompactSpace (symbolicLatentPathImage γ) :=
    isCompact_iff_compactSpace.mp (isCompact_symbolicLatentPathImage γ)
  exact CompHaus.of (symbolicLatentPathImage γ)

noncomputable def symbolicLatentPathImageMapCompHausIso
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    [T2Space X] [T2Space Y]
    (e : X ≃ₜ Y) (γ : SymbolicLatentPath X) :
    symbolicLatentPathImageCompHaus γ ≅
      symbolicLatentPathImageCompHaus
        (mapSymbolicLatentPathContinuous e e.continuous_toFun γ) := by
  dsimp [symbolicLatentPathImageCompHaus]
  letI : CompactSpace (symbolicLatentPathImage γ) :=
    isCompact_iff_compactSpace.mp (isCompact_symbolicLatentPathImage γ)
  letI : CompactSpace
      (symbolicLatentPathImage
        (mapSymbolicLatentPathContinuous e e.continuous_toFun γ)) :=
    isCompact_iff_compactSpace.mp
      (isCompact_symbolicLatentPathImage
        (mapSymbolicLatentPathContinuous e e.continuous_toFun γ))
  let h := symbolicLatentPathImageMapHomeomorph e γ
  exact
    { hom := ⟨TopCat.ofHom
        { toFun := h
          continuous_toFun := h.continuous_toFun }⟩
      inv := ⟨TopCat.ofHom
        { toFun := h.symm
          continuous_toFun := h.symm.continuous_toFun }⟩
      hom_inv_id := by
        apply ConcreteCategory.hom_ext
        intro x
        change h.symm (h x) = x
        exact h.symm_apply_apply x
      inv_hom_id := by
        apply ConcreteCategory.hom_ext
        intro y
        change h (h.symm y) = y
        exact h.apply_symm_apply y }

theorem symbolicLatentPathImageMapCompHausIso_hom_apply
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    [T2Space X] [T2Space Y]
    (e : X ≃ₜ Y) (γ : SymbolicLatentPath X)
    (x : symbolicLatentPathImage γ) :
    (symbolicLatentPathImageMapCompHausIso e γ).hom x =
      symbolicLatentPathImageMapHomeomorph e γ x :=
  rfl

theorem symbolicLatentPathImageMapCompHausIso_hom_forget
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    [T2Space X] [T2Space Y]
    (e : X ≃ₜ Y) (γ : SymbolicLatentPath X) :
    compHausToTop.map (symbolicLatentPathImageMapCompHausIso e γ).hom =
      symbolicLatentPathImageMapHomeomorphTopCatHom e γ := by
  apply TopCat.hom_ext
  ext x
  rfl

theorem symbolicLatentPathImageMapCompHausIso_trans_val
    {X Y Z : Type} [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace Z] [T2Space X] [T2Space Y] [T2Space Z]
    (e : X ≃ₜ Y) (f : Y ≃ₜ Z) (γ : SymbolicLatentPath X)
    (x : symbolicLatentPathImage γ) :
    (((symbolicLatentPathImageMapCompHausIso e γ).hom ≫
        (symbolicLatentPathImageMapCompHausIso f
          (mapSymbolicLatentPathContinuous e e.continuous_toFun γ)).hom) x).1 =
      ((symbolicLatentPathImageMapCompHausIso (e.trans f) γ).hom x).1 := by
  rfl

end
end InfoGeometry.Topology
