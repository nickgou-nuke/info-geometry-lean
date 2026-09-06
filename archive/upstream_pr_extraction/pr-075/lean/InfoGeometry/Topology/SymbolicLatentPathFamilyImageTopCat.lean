import Mathlib
import InfoGeometry.Topology.SymbolicLatentPathFamily

namespace InfoGeometry.Topology

open CategoryTheory

/-!
# `TopCat` factorization through a symbolic-latent path-family image

The image of a jointly continuous path family is a subtype of the ambient
feature space.  This owner packages the evaluation map into that subtype and
the canonical inclusion, so the image factorization is available directly in
`TopCat`.
-/

def symbolicLatentPathFamilyImageEvaluationTopCatHom
    {P X : Type} [TopologicalSpace P] [TopologicalSpace X]
    (H : SymbolicLatentPathFamily P X) :
    TopCat.of (P × SymbolicPathDomain) ⟶
      TopCat.of (symbolicLatentPathFamilyImage H) :=
  TopCat.ofHom
    { toFun := fun q => ⟨H q, ⟨q, rfl⟩⟩
      continuous_toFun := H.continuous.subtype_mk (fun q => ⟨q, rfl⟩) }

def symbolicLatentPathFamilyImageInclusionTopCatHom
    {P X : Type} [TopologicalSpace P] [TopologicalSpace X]
    (H : SymbolicLatentPathFamily P X) :
    TopCat.of (symbolicLatentPathFamilyImage H) ⟶ TopCat.of X :=
  TopCat.ofHom
    { toFun := Subtype.val
      continuous_toFun := continuous_subtype_val }

theorem symbolicLatentPathFamilyImage_evaluation_factorization
    {P X : Type} [TopologicalSpace P] [TopologicalSpace X]
    (H : SymbolicLatentPathFamily P X) :
    symbolicLatentPathFamilyImageEvaluationTopCatHom H ≫
        symbolicLatentPathFamilyImageInclusionTopCatHom H =
      TopCat.ofHom H := by
  ext q
  rfl

theorem symbolicLatentPathFamilyImage_evaluation_factorization_unique
    {P X : Type} [TopologicalSpace P] [TopologicalSpace X]
    (H : SymbolicLatentPathFamily P X)
    {u : TopCat.of (P × SymbolicPathDomain) ⟶
      TopCat.of (symbolicLatentPathFamilyImage H)}
    (hu : u ≫ symbolicLatentPathFamilyImageInclusionTopCatHom H =
      TopCat.ofHom H) :
    u = symbolicLatentPathFamilyImageEvaluationTopCatHom H := by
  apply TopCat.hom_ext
  ext q
  have hq := congrArg (fun m => m q) hu
  simpa [symbolicLatentPathFamilyImageEvaluationTopCatHom,
    symbolicLatentPathFamilyImageInclusionTopCatHom,
    TopCat.comp_app, TopCat.ofHom] using hq

end InfoGeometry.Topology
