import InfoGeometry.Topology.SymbolicLatentPathImageTransportTopCat
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Homeomorphic transport of symbolic-latent path images

An ambient homeomorphism restricts to a homeomorphism between the image of a
path and the image of its transported path.  This is the reversible upgrade
of the continuous path-image map; no such upgrade is asserted for a general
continuous map.
-/

namespace InfoGeometry.Topology

open CategoryTheory

noncomputable def symbolicLatentPathImageMapHomeomorph
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₜ Y) (γ : SymbolicLatentPath X) :
    symbolicLatentPathImage γ ≃ₜ
      symbolicLatentPathImage
        (mapSymbolicLatentPathContinuous e e.continuous_toFun γ) where
  toFun := fun x =>
    ⟨e x.1, by
      rw [symbolicLatentPathImage_map_eq_image e e.continuous_toFun γ]
      exact ⟨x.1, x.property, rfl⟩⟩
  invFun := fun y =>
    ⟨e.symm y.1, by
      rcases y.property with ⟨t, ht⟩
      refine ⟨t, ?_⟩
      rw [← ht]
      simpa using (e.symm_apply_apply (γ t)).symm
      ⟩
  left_inv := by
    intro x
    apply Subtype.ext
    exact e.symm_apply_apply x.1
  right_inv := by
    intro y
    apply Subtype.ext
    exact e.apply_symm_apply y.1
  continuous_toFun :=
    (e.continuous_toFun.comp continuous_subtype_val).subtype_mk _
  continuous_invFun :=
    (e.symm.continuous_toFun.comp continuous_subtype_val).subtype_mk _

@[simp] theorem symbolicLatentPathImageMapHomeomorph_apply
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₜ Y) (γ : SymbolicLatentPath X)
    (x : symbolicLatentPathImage γ) :
    symbolicLatentPathImageMapHomeomorph e γ x =
      ⟨e x.1, by
        rw [symbolicLatentPathImage_map_eq_image e e.continuous_toFun γ]
        exact ⟨x.1, x.property, rfl⟩⟩ :=
  rfl

noncomputable def symbolicLatentPathImageMapHomeomorphTopCatHom
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₜ Y) (γ : SymbolicLatentPath X) :
    TopCat.of (symbolicLatentPathImage γ) ⟶
      TopCat.of (symbolicLatentPathImage
        (mapSymbolicLatentPathContinuous e e.continuous_toFun γ)) :=
  TopCat.ofHom
    { toFun := symbolicLatentPathImageMapHomeomorph e γ
      continuous_toFun :=
        (symbolicLatentPathImageMapHomeomorph e γ).continuous_toFun }

theorem symbolicLatentPathImageMapHomeomorphTopCatHom_apply
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₜ Y) (γ : SymbolicLatentPath X)
    (x : symbolicLatentPathImage γ) :
    symbolicLatentPathImageMapHomeomorphTopCatHom e γ x =
      symbolicLatentPathImageMapHomeomorph e γ x :=
  rfl

theorem symbolicLatentPathImageMapHomeomorphTopCatHom_isIso
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₜ Y) (γ : SymbolicLatentPath X) :
    IsIso (symbolicLatentPathImageMapHomeomorphTopCatHom e γ) := by
  exact (TopCat.isIso_iff_isHomeomorph
    (symbolicLatentPathImageMapHomeomorphTopCatHom e γ)).2
      (symbolicLatentPathImageMapHomeomorph e γ).isHomeomorph

theorem symbolicLatentPathImageMapHomeomorph_trans_val
    {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace Z]
    (e : X ≃ₜ Y) (f : Y ≃ₜ Z) (γ : SymbolicLatentPath X)
    (x : symbolicLatentPathImage γ) :
    ((symbolicLatentPathImageMapHomeomorph e γ).trans
      (symbolicLatentPathImageMapHomeomorph f
        (mapSymbolicLatentPathContinuous e e.continuous_toFun γ)) x).1 =
      (symbolicLatentPathImageMapHomeomorph (e.trans f) γ x).1 := by
  rfl

end InfoGeometry.Topology
