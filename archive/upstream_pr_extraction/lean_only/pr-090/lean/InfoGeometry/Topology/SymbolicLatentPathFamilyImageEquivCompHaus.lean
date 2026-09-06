import InfoGeometry.Topology.SymbolicLatentPathFamilyImageCompHaus
import InfoGeometry.Topology.SymbolicLatentPathFamilyImageEquivTopCat
import Mathlib.Topology.Category.CompHaus.Basic

/-!
# Compact-Hausdorff transport of chart-equivalent path-family images

The chart-equivalence owner already supplies a homeomorphism of path-family
images.  This file packages that homeomorphism as a `CompHaus` isomorphism
when the parameter space is compact and the latent carriers are Hausdorff.
-/

noncomputable section

namespace InfoGeometry.Topology

open CategoryTheory

noncomputable def symbolicLatentPathFamilyImageCompHaus
    {P X : Type} [TopologicalSpace P] [TopologicalSpace X]
    [CompactSpace P] [T2Space X]
    (H : SymbolicLatentPathFamily P X) : CompHaus := by
  letI : CompactSpace (symbolicLatentPathFamilyImage H) :=
    isCompact_iff_compactSpace.mp
      (isCompact_symbolicLatentPathFamilyImage H)
  exact CompHaus.of (symbolicLatentPathFamilyImage H)

noncomputable def SymbolicLatentChartEquivalence.imageHomeomorphCompHausIso
    {P X Y : Type} [TopologicalSpace P] [TopologicalSpace X]
    [TopologicalSpace Y] [CompactSpace P] [T2Space X] [T2Space Y]
    {ι : Type} [Fintype ι]
    {C : SymbolicLatentChart X ι}
    {D : SymbolicLatentChart Y ι}
    (F : SymbolicLatentChartEquivalence C D)
    (H : SymbolicLatentPathFamily P X) :
    symbolicLatentPathFamilyImageCompHaus H ≅
      symbolicLatentPathFamilyImageCompHaus (F.mapFamily H) := by
  dsimp [symbolicLatentPathFamilyImageCompHaus]
  letI : CompactSpace (symbolicLatentPathFamilyImage H) :=
    isCompact_iff_compactSpace.mp
      (isCompact_symbolicLatentPathFamilyImage H)
  letI : CompactSpace
      (symbolicLatentPathFamilyImage (F.mapFamily H)) :=
    isCompact_iff_compactSpace.mp
      (isCompact_symbolicLatentPathFamilyImage (F.mapFamily H))
  let e := F.imageHomeomorph H
  exact
    { hom := ⟨TopCat.ofHom
        { toFun := e
          continuous_toFun := e.continuous_toFun }⟩
      inv := ⟨TopCat.ofHom
        { toFun := e.symm
          continuous_toFun := e.symm.continuous_toFun }⟩
      hom_inv_id := by
        apply ConcreteCategory.hom_ext
        intro x
        change e.symm (e x) = x
        exact e.symm_apply_apply x
      inv_hom_id := by
        apply ConcreteCategory.hom_ext
        intro y
        change e (e.symm y) = y
        exact e.apply_symm_apply y }

@[simp] theorem SymbolicLatentChartEquivalence.imageHomeomorphCompHausIso_hom_apply
    {P X Y : Type} [TopologicalSpace P] [TopologicalSpace X]
    [TopologicalSpace Y] [CompactSpace P] [T2Space X] [T2Space Y]
    {ι : Type} [Fintype ι]
    {C : SymbolicLatentChart X ι}
    {D : SymbolicLatentChart Y ι}
    (F : SymbolicLatentChartEquivalence C D)
    (H : SymbolicLatentPathFamily P X)
    (y : symbolicLatentPathFamilyImage H) :
    (F.imageHomeomorphCompHausIso H).hom y = F.imageHomeomorph H y :=
  rfl

theorem SymbolicLatentChartEquivalence.imageHomeomorphCompHausIso_hom_forget
    {P X Y : Type} [TopologicalSpace P] [TopologicalSpace X]
    [TopologicalSpace Y] [CompactSpace P] [T2Space X] [T2Space Y]
    {ι : Type} [Fintype ι]
    {C : SymbolicLatentChart X ι}
    {D : SymbolicLatentChart Y ι}
    (F : SymbolicLatentChartEquivalence C D)
    (H : SymbolicLatentPathFamily P X) :
    compHausToTop.map (F.imageHomeomorphCompHausIso H).hom =
      F.imageHomeomorphTopCatHom H := by
  apply TopCat.hom_ext
  ext y
  rfl

theorem SymbolicLatentChartEquivalence.imageHomeomorphCompHausIso_trans_val
    {P X Y Z : Type} [TopologicalSpace P] [TopologicalSpace X]
    [TopologicalSpace Y] [TopologicalSpace Z] [CompactSpace P]
    [T2Space X] [T2Space Y] [T2Space Z]
    {ι : Type} [Fintype ι]
    {C : SymbolicLatentChart X ι}
    {D : SymbolicLatentChart Y ι}
    {E : SymbolicLatentChart Z ι}
    (G : SymbolicLatentChartEquivalence D E)
    (F : SymbolicLatentChartEquivalence C D)
    (H : SymbolicLatentPathFamily P X)
    (x : symbolicLatentPathFamilyImage H) :
    (((F.imageHomeomorphCompHausIso H).hom ≫
        (G.imageHomeomorphCompHausIso (F.mapFamily H)).hom) x).1 =
      (((G.comp F).imageHomeomorphCompHausIso H).hom x).1 := by
  rfl

end InfoGeometry.Topology
