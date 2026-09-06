import Mathlib
import InfoGeometry.Topology.SymbolicLatentChartEquivalence

namespace InfoGeometry.Topology

open CategoryTheory

/-!
# `TopCat` readout of chart-equivalence transport on feasible regions

The underlying homeomorphism is owned by
`SymbolicLatentChartEquivalence.latentFeatureRegionHomeomorph`.  This file
only packages that native homeomorphism as a morphism of `TopCat`.
-/

def SymbolicLatentChartEquivalence.latentFeatureRegionTopCatHom
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    {ι : Type} [Fintype ι]
    {C : SymbolicLatentChart X ι}
    {D : SymbolicLatentChart Y ι}
    (F : SymbolicLatentChartEquivalence C D)
    (R : Set (SymbolicFeatureSpace ι)) :
    TopCat.of {x // x ∈ latentFeatureRegion C (F.featureEquiv ⁻¹' R)} ⟶
      TopCat.of {y // y ∈ latentFeatureRegion D R} :=
  TopCat.ofHom
    { toFun := latentFeatureRegionHomeomorph F R
      continuous_toFun :=
        (latentFeatureRegionHomeomorph F R).continuous_toFun }

def SymbolicLatentChartEquivalence.latentFeatureRegionInverseTopCatHom
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    {ι : Type} [Fintype ι]
    {C : SymbolicLatentChart X ι}
    {D : SymbolicLatentChart Y ι}
    (F : SymbolicLatentChartEquivalence C D)
    (R : Set (SymbolicFeatureSpace ι)) :
    TopCat.of {y // y ∈ latentFeatureRegion D R} ⟶
      TopCat.of {x // x ∈ latentFeatureRegion C (F.featureEquiv ⁻¹' R)} :=
  TopCat.ofHom
    { toFun := (latentFeatureRegionHomeomorph F R).symm
      continuous_toFun :=
        (latentFeatureRegionHomeomorph F R).symm.continuous_toFun }

@[simp] theorem SymbolicLatentChartEquivalence.latentFeatureRegionTopCatHom_apply
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    {ι : Type} [Fintype ι]
    {C : SymbolicLatentChart X ι}
    {D : SymbolicLatentChart Y ι}
    (F : SymbolicLatentChartEquivalence C D)
    (R : Set (SymbolicFeatureSpace ι))
    (x : {x // x ∈ latentFeatureRegion C (F.featureEquiv ⁻¹' R)}) :
    F.latentFeatureRegionTopCatHom R x =
      latentFeatureRegionHomeomorph F R x :=
  rfl

theorem SymbolicLatentChartEquivalence.latentFeatureRegionTopCatHom_isIso
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    {ι : Type} [Fintype ι]
    {C : SymbolicLatentChart X ι}
    {D : SymbolicLatentChart Y ι}
    (F : SymbolicLatentChartEquivalence C D)
    (R : Set (SymbolicFeatureSpace ι)) :
    IsIso (F.latentFeatureRegionTopCatHom R) := by
  refine IsIso.mk ⟨F.latentFeatureRegionInverseTopCatHom R, ?_, ?_⟩
  · apply TopCat.hom_ext
    ext y
    simpa [latentFeatureRegionTopCatHom,
      latentFeatureRegionInverseTopCatHom, TopCat.comp_app,
      TopCat.id_app, TopCat.ofHom] using
      congrArg Subtype.val ((latentFeatureRegionHomeomorph F R).symm_apply_apply y)
  · apply TopCat.hom_ext
    ext x
    simpa [latentFeatureRegionTopCatHom,
      latentFeatureRegionInverseTopCatHom, TopCat.comp_app,
      TopCat.id_app, TopCat.ofHom] using
      congrArg Subtype.val ((latentFeatureRegionHomeomorph F R).apply_symm_apply x)

theorem SymbolicLatentChartEquivalence.latentFeatureRegionTopCatHom_comp_inv
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    {ι : Type} [Fintype ι]
    {C : SymbolicLatentChart X ι}
    {D : SymbolicLatentChart Y ι}
    (F : SymbolicLatentChartEquivalence C D)
    (R : Set (SymbolicFeatureSpace ι)) :
    F.latentFeatureRegionTopCatHom R ≫
      F.latentFeatureRegionInverseTopCatHom R =
        𝟙 (TopCat.of {x // x ∈ latentFeatureRegion C (F.featureEquiv ⁻¹' R)}) := by
  apply TopCat.hom_ext
  ext x
  simpa [latentFeatureRegionTopCatHom,
    latentFeatureRegionInverseTopCatHom, TopCat.comp_app,
    TopCat.id_app, TopCat.ofHom] using
      congrArg Subtype.val ((latentFeatureRegionHomeomorph F R).symm_apply_apply x)

theorem SymbolicLatentChartEquivalence.latentFeatureRegionTopCatHom_inv_comp
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    {ι : Type} [Fintype ι]
    {C : SymbolicLatentChart X ι}
    {D : SymbolicLatentChart Y ι}
    (F : SymbolicLatentChartEquivalence C D)
    (R : Set (SymbolicFeatureSpace ι)) :
    F.latentFeatureRegionInverseTopCatHom R ≫
      F.latentFeatureRegionTopCatHom R =
        𝟙 (TopCat.of {y // y ∈ latentFeatureRegion D R}) := by
  apply TopCat.hom_ext
  ext x
  simpa [latentFeatureRegionTopCatHom,
    latentFeatureRegionInverseTopCatHom, TopCat.comp_app,
    TopCat.id_app, TopCat.ofHom] using
      congrArg Subtype.val ((latentFeatureRegionHomeomorph F R).apply_symm_apply x)

theorem SymbolicLatentChartEquivalence.latentFeatureRegionTopCatHom_comp
    {X Y Z : Type} [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace Z]
    {ι : Type} [Fintype ι]
    {C : SymbolicLatentChart X ι}
    {D : SymbolicLatentChart Y ι}
    {E : SymbolicLatentChart Z ι}
    (G : SymbolicLatentChartEquivalence D E)
    (F : SymbolicLatentChartEquivalence C D)
    (R : Set (SymbolicFeatureSpace ι)) :
    (G.comp F).latentFeatureRegionTopCatHom R =
      F.latentFeatureRegionTopCatHom (G.featureEquiv ⁻¹' R) ≫
        G.latentFeatureRegionTopCatHom R := by
  apply TopCat.hom_ext
  ext x
  rfl

@[simp] theorem SymbolicLatentChartEquivalence.latentFeatureRegionTopCatHom_comp_apply
    {X Y Z : Type} [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace Z]
    {ι : Type} [Fintype ι]
    {C : SymbolicLatentChart X ι}
    {D : SymbolicLatentChart Y ι}
    {E : SymbolicLatentChart Z ι}
    (G : SymbolicLatentChartEquivalence D E)
    (F : SymbolicLatentChartEquivalence C D)
    (R : Set (SymbolicFeatureSpace ι))
    (x : {x // x ∈ latentFeatureRegion C ((G.comp F).featureEquiv ⁻¹' R)}) :
    ((G.comp F).latentFeatureRegionTopCatHom R) x =
      (F.latentFeatureRegionTopCatHom (G.featureEquiv ⁻¹' R) ≫
        G.latentFeatureRegionTopCatHom R) x := by
  simpa [CategoryTheory.comp_apply] using
    congrArg (fun h => h x)
      (SymbolicLatentChartEquivalence.latentFeatureRegionTopCatHom_comp G F R)

theorem SymbolicLatentChartEquivalence.latentFeatureRegionInverseTopCatHom_comp
    {X Y Z : Type} [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace Z]
    {ι : Type} [Fintype ι]
    {C : SymbolicLatentChart X ι}
    {D : SymbolicLatentChart Y ι}
    {E : SymbolicLatentChart Z ι}
    (G : SymbolicLatentChartEquivalence D E)
    (F : SymbolicLatentChartEquivalence C D)
    (R : Set (SymbolicFeatureSpace ι)) :
    (G.comp F).latentFeatureRegionInverseTopCatHom R =
      G.latentFeatureRegionInverseTopCatHom R ≫
        F.latentFeatureRegionInverseTopCatHom (G.featureEquiv ⁻¹' R) := by
  apply TopCat.hom_ext
  ext x
  rfl

end InfoGeometry.Topology
