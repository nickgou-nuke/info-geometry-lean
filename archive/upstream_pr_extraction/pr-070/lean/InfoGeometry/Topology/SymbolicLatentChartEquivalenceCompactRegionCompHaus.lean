import InfoGeometry.Topology.SymbolicLatentChartEquivalenceCompactRegionTopCat
import Mathlib.Topology.Category.CompHaus.Basic

/-!
# Compact-Hausdorff chart-region equivalence

The chart-equivalence layer already proves compactness transport and a
`TopCat` isomorphism for feature regions.  With explicit Hausdorff
assumptions this owner packages the same local edge as a `CompHaus` iso.
-/

noncomputable section

namespace InfoGeometry.Topology

open CategoryTheory

noncomputable def SymbolicLatentChartEquivalence.latentFeatureRegionSourceCompHaus
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    {ι : Type} [Fintype ι] [T2Space X] [T2Space Y]
    {C : SymbolicLatentChart X ι}
    {D : SymbolicLatentChart Y ι}
    (F : SymbolicLatentChartEquivalence C D)
    (R : Set (SymbolicFeatureSpace ι))
    (hcompact : IsCompact
      (Set.univ : Set {x // x ∈ latentFeatureRegion C (F.featureEquiv ⁻¹' R)})) :
    CompHaus := by
  letI : CompactSpace
      {x // x ∈ latentFeatureRegion C (F.featureEquiv ⁻¹' R)} :=
    ⟨hcompact⟩
  exact CompHaus.of
    {x // x ∈ latentFeatureRegion C (F.featureEquiv ⁻¹' R)}

noncomputable def SymbolicLatentChartEquivalence.latentFeatureRegionTargetCompHaus
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    {ι : Type} [Fintype ι] [T2Space X] [T2Space Y]
    {C : SymbolicLatentChart X ι}
    {D : SymbolicLatentChart Y ι}
    (F : SymbolicLatentChartEquivalence C D)
    (R : Set (SymbolicFeatureSpace ι))
    (hcompact : IsCompact
      (Set.univ : Set {x // x ∈ latentFeatureRegion C (F.featureEquiv ⁻¹' R)})) :
    CompHaus := by
  have htarget := F.latentFeatureRegion_compact_transport R hcompact
  letI : CompactSpace {y // y ∈ latentFeatureRegion D R} :=
    ⟨htarget⟩
  exact CompHaus.of {y // y ∈ latentFeatureRegion D R}

noncomputable def SymbolicLatentChartEquivalence.latentFeatureRegionCompHausIso
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    {ι : Type} [Fintype ι] [T2Space X] [T2Space Y]
    {C : SymbolicLatentChart X ι}
    {D : SymbolicLatentChart Y ι}
    (F : SymbolicLatentChartEquivalence C D)
    (R : Set (SymbolicFeatureSpace ι))
    (hcompact : IsCompact
      (Set.univ : Set {x // x ∈ latentFeatureRegion C (F.featureEquiv ⁻¹' R)})) :
    F.latentFeatureRegionSourceCompHaus R hcompact ≅
      F.latentFeatureRegionTargetCompHaus R hcompact := by
  dsimp [latentFeatureRegionSourceCompHaus,
    latentFeatureRegionTargetCompHaus]
  letI : CompactSpace
      {x // x ∈ latentFeatureRegion C (F.featureEquiv ⁻¹' R)} :=
    ⟨hcompact⟩
  have htarget := F.latentFeatureRegion_compact_transport R hcompact
  letI : CompactSpace {y // y ∈ latentFeatureRegion D R} :=
    ⟨htarget⟩
  let e := latentFeatureRegionHomeomorph F R
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

@[simp] theorem SymbolicLatentChartEquivalence.latentFeatureRegionCompHausIso_hom_apply
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    {ι : Type} [Fintype ι] [T2Space X] [T2Space Y]
    {C : SymbolicLatentChart X ι}
    {D : SymbolicLatentChart Y ι}
    (F : SymbolicLatentChartEquivalence C D)
    (R : Set (SymbolicFeatureSpace ι))
    (hcompact : IsCompact
      (Set.univ : Set {x // x ∈ latentFeatureRegion C (F.featureEquiv ⁻¹' R)}))
    (x : {x // x ∈ latentFeatureRegion C (F.featureEquiv ⁻¹' R)}) :
    (F.latentFeatureRegionCompHausIso R hcompact).hom x =
      latentFeatureRegionHomeomorph F R x :=
  rfl

theorem SymbolicLatentChartEquivalence.latentFeatureRegionCompHausIso_hom_forget
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    {ι : Type} [Fintype ι] [T2Space X] [T2Space Y]
    {C : SymbolicLatentChart X ι}
    {D : SymbolicLatentChart Y ι}
    (F : SymbolicLatentChartEquivalence C D)
    (R : Set (SymbolicFeatureSpace ι))
    (hcompact : IsCompact
      (Set.univ : Set {x // x ∈ latentFeatureRegion C (F.featureEquiv ⁻¹' R)})) :
    compHausToTop.map (F.latentFeatureRegionCompHausIso R hcompact).hom =
      F.latentFeatureRegionTopCatHom R := by
  rfl

end InfoGeometry.Topology

end
