import Mathlib
import InfoGeometry.Topology.SymbolicLatentPathFamilyImageEquiv

namespace InfoGeometry.Topology

open CategoryTheory

/-!
# Categorical image equivalence for chart-equivalent path families

The homeomorphism of family images is exposed as a `TopCat` morphism and
certified with the native `IsIso` predicate.  Thus the image transport is not
merely a pointwise equivalence: it is an isomorphism in the topological
category.
-/

def SymbolicLatentChartEquivalence.imageHomeomorphTopCatHom
    {P X Y : Type} [TopologicalSpace P] [TopologicalSpace X]
    [TopologicalSpace Y]
    {ι : Type} [Fintype ι]
    {C : SymbolicLatentChart X ι}
    {D : SymbolicLatentChart Y ι}
    (F : SymbolicLatentChartEquivalence C D)
    (H : SymbolicLatentPathFamily P X) :
    TopCat.of (symbolicLatentPathFamilyImage H) ⟶
      TopCat.of (symbolicLatentPathFamilyImage (F.mapFamily H)) :=
  TopCat.ofHom
    { toFun := F.imageHomeomorph H
      continuous_toFun := (F.imageHomeomorph H).continuous_toFun }

def SymbolicLatentChartEquivalence.imageHomeomorphInverseTopCatHom
    {P X Y : Type} [TopologicalSpace P] [TopologicalSpace X]
    [TopologicalSpace Y]
    {ι : Type} [Fintype ι]
    {C : SymbolicLatentChart X ι}
    {D : SymbolicLatentChart Y ι}
    (F : SymbolicLatentChartEquivalence C D)
    (H : SymbolicLatentPathFamily P X) :
    TopCat.of (symbolicLatentPathFamilyImage (F.mapFamily H)) ⟶
      TopCat.of (symbolicLatentPathFamilyImage H) :=
  TopCat.ofHom
    { toFun := (F.imageHomeomorph H).symm
      continuous_toFun := (F.imageHomeomorph H).symm.continuous_toFun }

@[simp] theorem SymbolicLatentChartEquivalence.imageHomeomorphTopCatHom_apply
    {P X Y : Type} [TopologicalSpace P] [TopologicalSpace X]
    [TopologicalSpace Y]
    {ι : Type} [Fintype ι]
    {C : SymbolicLatentChart X ι}
    {D : SymbolicLatentChart Y ι}
    (F : SymbolicLatentChartEquivalence C D)
    (H : SymbolicLatentPathFamily P X)
    (y : symbolicLatentPathFamilyImage H) :
    F.imageHomeomorphTopCatHom H y = F.imageHomeomorph H y :=
  rfl

theorem SymbolicLatentChartEquivalence.imageHomeomorphTopCatHom_isIso
    {P X Y : Type} [TopologicalSpace P] [TopologicalSpace X]
    [TopologicalSpace Y]
    {ι : Type} [Fintype ι]
    {C : SymbolicLatentChart X ι}
    {D : SymbolicLatentChart Y ι}
    (F : SymbolicLatentChartEquivalence C D)
    (H : SymbolicLatentPathFamily P X) :
    IsIso (F.imageHomeomorphTopCatHom H) := by
  refine IsIso.mk ⟨F.imageHomeomorphInverseTopCatHom H, ?_, ?_⟩
  · apply TopCat.hom_ext
    ext y
    simpa [imageHomeomorphTopCatHom,
      imageHomeomorphInverseTopCatHom, TopCat.comp_app,
      TopCat.id_app, TopCat.ofHom] using
      congrArg Subtype.val ((F.imageHomeomorph H).symm_apply_apply y)
  · apply TopCat.hom_ext
    ext y
    simpa [imageHomeomorphTopCatHom,
      imageHomeomorphInverseTopCatHom, TopCat.comp_app,
      TopCat.id_app, TopCat.ofHom] using
      congrArg Subtype.val ((F.imageHomeomorph H).apply_symm_apply y)

end InfoGeometry.Topology
