import InfoGeometry.Topology.SymbolicLatentAtlasOverlapFeatureRegionTopCat
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Topology.Category.CompHaus.Basic

/-!
# Compact-Hausdorff transport of overlap feature regions

The overlap feature-region owner already proves that the source and target
subtypes are homeomorphic.  This file packages that homeomorphism in
`CompHaus` under an explicit compactness property for the source region.
-/

noncomputable section

namespace InfoGeometry.Topology

open CategoryTheory

noncomputable def SymbolicLatentAtlas.overlapFeatureRegionSourceCompHaus
    {X ι κ : Type} [TopologicalSpace X] [Fintype ι] [Fintype κ]
    [T2Space X]
    (A : SymbolicLatentAtlas X ι κ)
    {i j : κ} (H : SymbolicLatentAtlasCompatibility A i j)
    (R : Set (SymbolicFeatureSpace ι))
    (hcompact : IsCompact (A.overlapFeatureRegionSource H R)) : CompHaus := by
  letI : CompactSpace {x // x ∈ A.overlapFeatureRegionSource H R} :=
    isCompact_iff_compactSpace.mp hcompact
  exact CompHaus.of {x // x ∈ A.overlapFeatureRegionSource H R}

noncomputable def SymbolicLatentAtlas.overlapFeatureRegionTargetCompHaus
    {X ι κ : Type} [TopologicalSpace X] [Fintype ι] [Fintype κ]
    [T2Space X]
    (A : SymbolicLatentAtlas X ι κ)
    {i j : κ} (H : SymbolicLatentAtlasCompatibility A i j)
    (R : Set (SymbolicFeatureSpace ι))
    (hcompact : IsCompact (A.overlapFeatureRegionSource H R)) : CompHaus := by
  have htarget : IsCompact (A.overlapFeatureRegionTarget H R) := by
    rw [← A.overlapFeatureRegionSource_eq_target H R]
    exact hcompact
  letI : CompactSpace {x // x ∈ A.overlapFeatureRegionTarget H R} :=
    isCompact_iff_compactSpace.mp htarget
  exact CompHaus.of {x // x ∈ A.overlapFeatureRegionTarget H R}

noncomputable def SymbolicLatentAtlas.overlapFeatureRegionCompHausIso
    {X ι κ : Type} [TopologicalSpace X] [Fintype ι] [Fintype κ]
    [T2Space X]
    (A : SymbolicLatentAtlas X ι κ)
    {i j : κ} (H : SymbolicLatentAtlasCompatibility A i j)
    (R : Set (SymbolicFeatureSpace ι))
    (hcompact : IsCompact (A.overlapFeatureRegionSource H R)) :
    A.overlapFeatureRegionSourceCompHaus H R hcompact ≅
      A.overlapFeatureRegionTargetCompHaus H R hcompact := by
  dsimp [overlapFeatureRegionSourceCompHaus,
    overlapFeatureRegionTargetCompHaus]
  letI : CompactSpace {x // x ∈ A.overlapFeatureRegionSource H R} :=
    isCompact_iff_compactSpace.mp hcompact
  have htarget : IsCompact (A.overlapFeatureRegionTarget H R) := by
    rw [← A.overlapFeatureRegionSource_eq_target H R]
    exact hcompact
  letI : CompactSpace {x // x ∈ A.overlapFeatureRegionTarget H R} :=
    isCompact_iff_compactSpace.mp htarget
  let e := A.overlapFeatureRegionHomeomorph H R
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

@[simp] theorem SymbolicLatentAtlas.overlapFeatureRegionCompHausIso_hom_apply
    {X ι κ : Type} [TopologicalSpace X] [Fintype ι] [Fintype κ]
    [T2Space X]
    (A : SymbolicLatentAtlas X ι κ)
    {i j : κ} (H : SymbolicLatentAtlasCompatibility A i j)
    (R : Set (SymbolicFeatureSpace ι))
    (hcompact : IsCompact (A.overlapFeatureRegionSource H R))
    (x : {x // x ∈ A.overlapFeatureRegionSource H R}) :
    (A.overlapFeatureRegionCompHausIso H R hcompact).hom x =
      A.overlapFeatureRegionHomeomorph H R x :=
  rfl

theorem SymbolicLatentAtlas.overlapFeatureRegionCompHausIso_hom_forget
    {X ι κ : Type} [TopologicalSpace X] [Fintype ι] [Fintype κ]
    [T2Space X]
    (A : SymbolicLatentAtlas X ι κ)
    {i j : κ} (H : SymbolicLatentAtlasCompatibility A i j)
    (R : Set (SymbolicFeatureSpace ι))
    (hcompact : IsCompact (A.overlapFeatureRegionSource H R)) :
    compHausToTop.map (A.overlapFeatureRegionCompHausIso H R hcompact).hom =
      A.overlapFeatureRegionTopCatHom H R := by
  apply TopCat.hom_ext
  ext x
  rfl

end InfoGeometry.Topology
