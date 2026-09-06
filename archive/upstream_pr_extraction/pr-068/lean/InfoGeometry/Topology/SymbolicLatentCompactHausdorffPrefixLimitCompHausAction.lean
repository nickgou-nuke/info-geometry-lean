import InfoGeometry.Topology.SymbolicLatentCompactHausdorffPrefixLimitAction
import InfoGeometry.Topology.SymbolicLatentBoundaryInverseLimitCompHaus
import Mathlib.Topology.Category.CompHaus.Basic

/-!
# `CompHaus` action on the compact prefix-limit carrier

The native coordinatewise action is already constructed on the boundary and
transported to the inverse-limit object as a `Homeomorph`.  This owner carries
the same action through the genuine compact-Hausdorff isomorphism, so its
composition and identity laws are proved in `CompHaus` itself.
-/

noncomputable section

namespace InfoGeometry.Topology

open CategoryTheory
open InfoGeometry.Topology.NaryTreeBoundaryCompactHausdorffCoordinatewiseAction
open InfoGeometry.Topology.SymbolicLatentCompactHausdorffPrefixLimitAction

variable {A : Type} [TopologicalSpace A] [CompactSpace A] [T2Space A]

noncomputable def symbolicBoundaryCoordinatewiseCompHausIso
    (γ : A ≃ₜ A) :
    symbolicBoundaryCompHaus (A := A) ≅ symbolicBoundaryCompHaus (A := A) :=
  { hom := ⟨TopCat.ofHom
        { toFun := boundaryCoordinatewiseHomeomorph γ
          continuous_toFun := (boundaryCoordinatewiseHomeomorph γ).continuous_toFun }⟩
    inv := ⟨TopCat.ofHom
        { toFun := (boundaryCoordinatewiseHomeomorph γ).symm
          continuous_toFun := (boundaryCoordinatewiseHomeomorph γ).symm.continuous_toFun }⟩
    hom_inv_id := by
      apply ConcreteCategory.hom_ext
      intro x
      change (boundaryCoordinatewiseHomeomorph γ).symm
          (boundaryCoordinatewiseHomeomorph γ x) = x
      exact (boundaryCoordinatewiseHomeomorph γ).symm_apply_apply x
    inv_hom_id := by
      apply ConcreteCategory.hom_ext
      intro x
      change boundaryCoordinatewiseHomeomorph γ
          ((boundaryCoordinatewiseHomeomorph γ).symm x) = x
      exact (boundaryCoordinatewiseHomeomorph γ).apply_symm_apply x }

noncomputable def symbolicBoundaryPrefixLimitCoordinatewiseCompHausIso
    (γ : A ≃ₜ A) :
    symbolicBoundaryPrefixLimitCompHaus (A := A) ≅
      symbolicBoundaryPrefixLimitCompHaus (A := A) := by
  let e := symbolicBoundaryPrefixLimitCompHausIso (A := A)
  exact (e.symm.trans (symbolicBoundaryCoordinatewiseCompHausIso (A := A) γ)).trans e

theorem symbolicBoundaryPrefixLimitCoordinatewiseCompHausIso_hom_apply
    (γ : A ≃ₜ A)
    (x : symbolicBoundaryPrefixLimitCompHaus (A := A)) :
    (symbolicBoundaryPrefixLimitCoordinatewiseCompHausIso (A := A) γ).hom x =
      prefixLimitCoordinatewiseHomeomorph (A := A) γ x := by
  rfl

theorem symbolicBoundaryPrefixLimitCoordinatewiseCompHausIso_trans
    (γ δ : A ≃ₜ A) :
    (symbolicBoundaryPrefixLimitCoordinatewiseCompHausIso (A := A) γ).hom ≫
        (symbolicBoundaryPrefixLimitCoordinatewiseCompHausIso (A := A) δ).hom =
      (symbolicBoundaryPrefixLimitCoordinatewiseCompHausIso (A := A) (γ.trans δ)).hom := by
  apply ConcreteCategory.hom_ext
  intro x
  change
    (symbolicBoundaryPrefixLimitCoordinatewiseCompHausIso (A := A) δ).hom
        ((symbolicBoundaryPrefixLimitCoordinatewiseCompHausIso (A := A) γ).hom x) =
      (symbolicBoundaryPrefixLimitCoordinatewiseCompHausIso (A := A) (γ.trans δ)).hom x
  rw [symbolicBoundaryPrefixLimitCoordinatewiseCompHausIso_hom_apply,
    symbolicBoundaryPrefixLimitCoordinatewiseCompHausIso_hom_apply,
    symbolicBoundaryPrefixLimitCoordinatewiseCompHausIso_hom_apply]
  exact congrArg (fun h => h x)
    (prefixLimitCoordinatewiseHomeomorph_trans (A := A) γ δ)

theorem symbolicBoundaryPrefixLimitCoordinatewiseCompHausIso_refl :
    symbolicBoundaryPrefixLimitCoordinatewiseCompHausIso (A := A)
        (Homeomorph.refl A) = Iso.refl _ := by
  apply Iso.ext
  apply ConcreteCategory.hom_ext
  intro x
  change
    (symbolicBoundaryPrefixLimitCoordinatewiseCompHausIso (A := A)
      (Homeomorph.refl A)).hom x = x
  rw [symbolicBoundaryPrefixLimitCoordinatewiseCompHausIso_hom_apply]
  rw [prefixLimitCoordinatewiseHomeomorph_apply]
  simpa [boundaryCoordinatewiseHomeomorph] using
    (TopCat.homeoOfIso (prefixBoundaryLimitIso (A := A))).apply_symm_apply x

end InfoGeometry.Topology
