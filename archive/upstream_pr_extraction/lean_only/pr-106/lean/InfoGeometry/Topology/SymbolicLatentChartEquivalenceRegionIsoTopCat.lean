import InfoGeometry.Topology.SymbolicLatentChartEquivalenceRegionTopCat

namespace InfoGeometry.Topology

open CategoryTheory

/-!
# Native `TopCat` isomorphism for equivalent chart regions

The preceding owner proves `IsIso` for the continuous chart-region map.  This
bridge exposes the corresponding categorical `Iso`, so downstream colimit and
transport constructions can use the standard Mathlib isomorphism API.
-/

noncomputable def SymbolicLatentChartEquivalence.latentFeatureRegionTopCatIso
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    {ι : Type} [Fintype ι]
    {C : SymbolicLatentChart X ι}
    {D : SymbolicLatentChart Y ι}
    (F : SymbolicLatentChartEquivalence C D)
    (R : Set (SymbolicFeatureSpace ι)) :
    TopCat.of {x // x ∈ latentFeatureRegion C (F.featureEquiv ⁻¹' R)} ≅
      TopCat.of {y // y ∈ latentFeatureRegion D R} := by
  refine
    { hom := F.latentFeatureRegionTopCatHom R
      inv := F.latentFeatureRegionInverseTopCatHom R
      hom_inv_id := ?_
      inv_hom_id := ?_ }
  · apply TopCat.hom_ext
    ext y
    simpa [SymbolicLatentChartEquivalence.latentFeatureRegionTopCatHom,
      SymbolicLatentChartEquivalence.latentFeatureRegionInverseTopCatHom,
      TopCat.comp_app, TopCat.id_app, TopCat.ofHom] using
      congrArg Subtype.val
        ((latentFeatureRegionHomeomorph F R).symm_apply_apply y)
  · apply TopCat.hom_ext
    ext x
    simpa [SymbolicLatentChartEquivalence.latentFeatureRegionTopCatHom,
      SymbolicLatentChartEquivalence.latentFeatureRegionInverseTopCatHom,
      TopCat.comp_app, TopCat.id_app, TopCat.ofHom] using
      congrArg Subtype.val
        ((latentFeatureRegionHomeomorph F R).apply_symm_apply x)

@[simp] theorem SymbolicLatentChartEquivalence.latentFeatureRegionTopCatIso_hom
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    {ι : Type} [Fintype ι]
    {C : SymbolicLatentChart X ι}
    {D : SymbolicLatentChart Y ι}
    (F : SymbolicLatentChartEquivalence C D)
    (R : Set (SymbolicFeatureSpace ι)) :
    (F.latentFeatureRegionTopCatIso R).hom =
      F.latentFeatureRegionTopCatHom R := by
  rfl

@[simp] theorem SymbolicLatentChartEquivalence.latentFeatureRegionTopCatIso_inv
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    {ι : Type} [Fintype ι]
    {C : SymbolicLatentChart X ι}
    {D : SymbolicLatentChart Y ι}
    (F : SymbolicLatentChartEquivalence C D)
    (R : Set (SymbolicFeatureSpace ι)) :
    (F.latentFeatureRegionTopCatIso R).inv =
      F.latentFeatureRegionInverseTopCatHom R := by
  simp [SymbolicLatentChartEquivalence.latentFeatureRegionTopCatIso]

end InfoGeometry.Topology
