import Mathlib
import InfoGeometry.Topology.SymbolicLatentPathFamilyImageTopCat

namespace InfoGeometry.Topology

open CategoryTheory

/-!
# Region-valued factorization for a symbolic-latent path-family image

If a jointly continuous family is known to stay in a region, its image subtype
maps canonically to the region subtype.  This keeps the region restriction
visible in `TopCat` while retaining the ambient image factorization.
-/

def symbolicLatentPathFamilyImageToRegionTopCatHom
    {P X : Type} [TopologicalSpace P] [TopologicalSpace X]
    (H : SymbolicLatentPathFamily P X) (R : Set X)
    (hF : H.InRegion R) :
    TopCat.of (symbolicLatentPathFamilyImage H) ⟶ TopCat.of R :=
  TopCat.ofHom
    { toFun := fun y =>
        ⟨y.1, by
          rcases y.2 with ⟨q, hq⟩
          rw [← hq]
          exact hF q.1 q.2⟩
      continuous_toFun :=
        continuous_subtype_val.subtype_mk (fun y => by
          rcases y.2 with ⟨q, hq⟩
          rw [← hq]
          exact hF q.1 q.2) }

def symbolicLatentPathFamilyToRegionTopCatHom
    {P X : Type} [TopologicalSpace P] [TopologicalSpace X]
    (H : SymbolicLatentPathFamily P X) (R : Set X)
    (hF : H.InRegion R) :
    TopCat.of (P × SymbolicPathDomain) ⟶ TopCat.of R :=
  TopCat.ofHom
    { toFun := fun q => ⟨H q, hF q.1 q.2⟩
      continuous_toFun := H.continuous.subtype_mk (fun q => hF q.1 q.2) }

def symbolicLatentRegionInclusionTopCatHom
    {X : Type} [TopologicalSpace X] (R : Set X) :
    TopCat.of R ⟶ TopCat.of X :=
  TopCat.ofHom
    { toFun := Subtype.val
      continuous_toFun := continuous_subtype_val }

theorem symbolicLatentPathFamilyImage_toRegion_factorization
    {P X : Type} [TopologicalSpace P] [TopologicalSpace X]
    (H : SymbolicLatentPathFamily P X) (R : Set X)
    (hF : H.InRegion R) :
    symbolicLatentPathFamilyImageEvaluationTopCatHom H ≫
        symbolicLatentPathFamilyImageToRegionTopCatHom H R hF =
      symbolicLatentPathFamilyToRegionTopCatHom H R hF := by
  ext q
  rfl

theorem symbolicLatentPathFamilyImage_region_inclusion_factorization
    {P X : Type} [TopologicalSpace P] [TopologicalSpace X]
    (H : SymbolicLatentPathFamily P X) (R : Set X)
    (hF : H.InRegion R) :
    symbolicLatentPathFamilyImageToRegionTopCatHom H R hF ≫
        symbolicLatentRegionInclusionTopCatHom R =
      symbolicLatentPathFamilyImageInclusionTopCatHom H := by
  ext y
  rfl

theorem symbolicLatentPathFamilyImage_toRegion_unique
    {P X : Type} [TopologicalSpace P] [TopologicalSpace X]
    (H : SymbolicLatentPathFamily P X) (R : Set X)
    (hF : H.InRegion R)
    {u : TopCat.of (symbolicLatentPathFamilyImage H) ⟶ TopCat.of R}
    (hu : u ≫ symbolicLatentRegionInclusionTopCatHom R =
      symbolicLatentPathFamilyImageInclusionTopCatHom H) :
    u = symbolicLatentPathFamilyImageToRegionTopCatHom H R hF := by
  apply TopCat.hom_ext
  ext y
  have hy := congrArg (fun m => m y) hu
  simpa [symbolicLatentPathFamilyImageToRegionTopCatHom,
    symbolicLatentRegionInclusionTopCatHom,
    symbolicLatentPathFamilyImageInclusionTopCatHom,
    TopCat.comp_app, TopCat.ofHom] using hy

end InfoGeometry.Topology
