import InfoGeometry.Topology.SymbolicLatentAtlasOverlapTopCat
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# TopCat transport of atlas overlap feature regions

An atlas compatibility intertwines observations only on the chart overlap.
Consequently, the honest local transport is between the two overlap-restricted
feature regions, not between unrestricted chart domains.  The carrier map is
the identity on the common underlying points, packaged as a native
`Homeomorph` and then as an `IsIso` in `TopCat`.
-/

namespace InfoGeometry.Topology

open CategoryTheory

def SymbolicLatentAtlas.overlapFeatureRegionSource
    {X : Type} [TopologicalSpace X]
    {ι κ : Type} [Fintype ι] [Fintype κ]
    (A : SymbolicLatentAtlas X ι κ)
    {i j : κ} (H : SymbolicLatentAtlasCompatibility A i j)
    (R : Set (SymbolicFeatureSpace ι)) : Set X :=
  A.overlap i j ∩ latentFeatureRegion (A.chart i)
    (H.featureEquiv ⁻¹' R)

def SymbolicLatentAtlas.overlapFeatureRegionTarget
    {X : Type} [TopologicalSpace X]
    {ι κ : Type} [Fintype ι] [Fintype κ]
    (A : SymbolicLatentAtlas X ι κ)
    {i j : κ} (H : SymbolicLatentAtlasCompatibility A i j)
    (R : Set (SymbolicFeatureSpace ι)) : Set X :=
  A.overlap i j ∩ latentFeatureRegion (A.chart j) R

theorem SymbolicLatentAtlas.overlapFeatureRegionSource_eq_target
    {X : Type} [TopologicalSpace X]
    {ι κ : Type} [Fintype ι] [Fintype κ]
    (A : SymbolicLatentAtlas X ι κ)
    {i j : κ} (H : SymbolicLatentAtlasCompatibility A i j)
    (R : Set (SymbolicFeatureSpace ι)) :
    A.overlapFeatureRegionSource H R =
      A.overlapFeatureRegionTarget H R := by
  ext x
  constructor
  · intro hx
    refine ⟨hx.1, ?_⟩
    change symbolicObservationMap (A.chart j).system x ∈ R
    rw [← H.intertwines_on_overlap x hx.1]
    exact hx.2
  · intro hx
    refine ⟨hx.1, ?_⟩
    change H.featureEquiv (symbolicObservationMap (A.chart i).system x) ∈ R
    rw [H.intertwines_on_overlap x hx.1]
    exact hx.2

noncomputable def SymbolicLatentAtlas.overlapFeatureRegionHomeomorph
    {X : Type} [TopologicalSpace X]
    {ι κ : Type} [Fintype ι] [Fintype κ]
    (A : SymbolicLatentAtlas X ι κ)
    {i j : κ} (H : SymbolicLatentAtlasCompatibility A i j)
    (R : Set (SymbolicFeatureSpace ι)) :
    {x // x ∈ A.overlapFeatureRegionSource H R} ≃ₜ
      {x // x ∈ A.overlapFeatureRegionTarget H R} :=
  Homeomorph.setCongr (A.overlapFeatureRegionSource_eq_target H R)

noncomputable def SymbolicLatentAtlas.overlapFeatureRegionTopCatHom
    {X : Type} [TopologicalSpace X]
    {ι κ : Type} [Fintype ι] [Fintype κ]
    (A : SymbolicLatentAtlas X ι κ)
    {i j : κ} (H : SymbolicLatentAtlasCompatibility A i j)
    (R : Set (SymbolicFeatureSpace ι)) :
    TopCat.of {x // x ∈ A.overlapFeatureRegionSource H R} ⟶
      TopCat.of {x // x ∈ A.overlapFeatureRegionTarget H R} :=
  TopCat.ofHom
    { toFun := A.overlapFeatureRegionHomeomorph H R
      continuous_toFun :=
        (A.overlapFeatureRegionHomeomorph H R).continuous_toFun }

noncomputable def SymbolicLatentAtlas.overlapFeatureRegionTopCatHomInv
    {X : Type} [TopologicalSpace X]
    {ι κ : Type} [Fintype ι] [Fintype κ]
    (A : SymbolicLatentAtlas X ι κ)
    {i j : κ} (H : SymbolicLatentAtlasCompatibility A i j)
    (R : Set (SymbolicFeatureSpace ι)) :
    TopCat.of {x // x ∈ A.overlapFeatureRegionTarget H R} ⟶
      TopCat.of {x // x ∈ A.overlapFeatureRegionSource H R} :=
  TopCat.ofHom
    { toFun := (A.overlapFeatureRegionHomeomorph H R).symm
      continuous_toFun :=
        (A.overlapFeatureRegionHomeomorph H R).symm.continuous_toFun }

theorem SymbolicLatentAtlas.overlapFeatureRegionTopCatHom_isIso
    {X : Type} [TopologicalSpace X]
    {ι κ : Type} [Fintype ι] [Fintype κ]
    (A : SymbolicLatentAtlas X ι κ)
    {i j : κ} (H : SymbolicLatentAtlasCompatibility A i j)
    (R : Set (SymbolicFeatureSpace ι)) :
    IsIso (A.overlapFeatureRegionTopCatHom H R) := by
  let e := A.overlapFeatureRegionHomeomorph H R
  refine IsIso.mk ⟨TopCat.ofHom
    { toFun := e.symm
      continuous_toFun := e.symm.continuous_toFun }, ?_, ?_⟩
  · apply TopCat.hom_ext
    ext x
    exact congrArg Subtype.val (e.symm_apply_apply x)
  · apply TopCat.hom_ext
    ext x
    exact congrArg Subtype.val (e.apply_symm_apply x)

theorem SymbolicLatentAtlas.overlapFeatureRegionTopCatHom_comp_inv
    {X : Type} [TopologicalSpace X]
    {ι κ : Type} [Fintype ι] [Fintype κ]
    (A : SymbolicLatentAtlas X ι κ)
    {i j : κ} (H : SymbolicLatentAtlasCompatibility A i j)
    (R : Set (SymbolicFeatureSpace ι)) :
    A.overlapFeatureRegionTopCatHom H R ≫
        A.overlapFeatureRegionTopCatHomInv H R =
      𝟙 (TopCat.of {x // x ∈ A.overlapFeatureRegionSource H R}) := by
  apply TopCat.hom_ext
  ext x
  exact congrArg Subtype.val
    ((A.overlapFeatureRegionHomeomorph H R).symm_apply_apply x)

theorem SymbolicLatentAtlas.overlapFeatureRegionTopCatHom_inv_comp
    {X : Type} [TopologicalSpace X]
    {ι κ : Type} [Fintype ι] [Fintype κ]
    (A : SymbolicLatentAtlas X ι κ)
    {i j : κ} (H : SymbolicLatentAtlasCompatibility A i j)
    (R : Set (SymbolicFeatureSpace ι)) :
    A.overlapFeatureRegionTopCatHomInv H R ≫
        A.overlapFeatureRegionTopCatHom H R =
      𝟙 (TopCat.of {x // x ∈ A.overlapFeatureRegionTarget H R}) := by
  apply TopCat.hom_ext
  ext x
  exact congrArg Subtype.val
    ((A.overlapFeatureRegionHomeomorph H R).apply_symm_apply x)

end InfoGeometry.Topology
