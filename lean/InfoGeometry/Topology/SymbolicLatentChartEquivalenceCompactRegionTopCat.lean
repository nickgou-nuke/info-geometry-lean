import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Topology.SymbolicLatentChartEquivalenceRegionTopCat

namespace InfoGeometry.Topology

/-!
# Compactness transport for equivalent chart regions

The chart-equivalence owner supplies a genuine homeomorphism between the two
feature regions.  This bridge records the corresponding compactness transport
without asserting compactness of either chart domain unconditionally.
-/

theorem SymbolicLatentChartEquivalence.latentFeatureRegion_compact_transport
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    {ι : Type} [Fintype ι]
    {C : SymbolicLatentChart X ι}
    {D : SymbolicLatentChart Y ι}
    (F : SymbolicLatentChartEquivalence C D)
    (R : Set (SymbolicFeatureSpace ι))
    (hsource : IsCompact
      (Set.univ : Set {x // x ∈ latentFeatureRegion C (F.featureEquiv ⁻¹' R)})) :
    IsCompact
      (Set.univ : Set {y // y ∈ latentFeatureRegion D R}) := by
  have himage := hsource.image
    (latentFeatureRegionHomeomorph F R).continuous_toFun
  rw [Set.image_univ_of_surjective
    (f := (latentFeatureRegionHomeomorph F R).toFun)
    (latentFeatureRegionHomeomorph F R).surjective] at himage
  exact himage

theorem SymbolicLatentChartEquivalence.latentFeatureRegion_compact_transport_homeomorph
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    {ι : Type} [Fintype ι]
    {C : SymbolicLatentChart X ι}
    {D : SymbolicLatentChart Y ι}
    (F : SymbolicLatentChartEquivalence C D)
    (R : Set (SymbolicFeatureSpace ι))
    (hsource : CompactSpace
      {x // x ∈ latentFeatureRegion C (F.featureEquiv ⁻¹' R)}) :
    CompactSpace {y // y ∈ latentFeatureRegion D R} := by
  letI : CompactSpace
      {y // y ∈ latentFeatureRegion D R} :=
    ⟨by
      simpa only [isCompact_univ] using
        F.latentFeatureRegion_compact_transport R isCompact_univ⟩
  infer_instance

theorem SymbolicLatentChartEquivalence.latentFeatureRegion_compact_transport_iff
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    {ι : Type} [Fintype ι]
    {C : SymbolicLatentChart X ι}
    {D : SymbolicLatentChart Y ι}
    (F : SymbolicLatentChartEquivalence C D)
    (R : Set (SymbolicFeatureSpace ι)) :
    IsCompact
        (Set.univ : Set {x // x ∈ latentFeatureRegion C (F.featureEquiv ⁻¹' R)}) ↔
      IsCompact
        (Set.univ : Set {y // y ∈ latentFeatureRegion D R}) := by
  constructor
  · intro hsource
    exact F.latentFeatureRegion_compact_transport R hsource
  · intro htarget
    have hpreimage :
        F.featureEquiv.toEquiv.symm ⁻¹' (F.featureEquiv.toEquiv ⁻¹' R) = R := by
      simpa using (Equiv.symm_preimage_preimage F.featureEquiv.toEquiv R)
    have hsource :
        IsCompact
          (Set.univ : Set
            {x // x ∈ latentFeatureRegion D
              (F.featureEquiv.toEquiv.symm ⁻¹' (F.featureEquiv.toEquiv ⁻¹' R))}) := by
      rw [hpreimage]
      exact htarget
    simpa using
      (SymbolicLatentChartEquivalence.latentFeatureRegion_compact_transport
        (F := F.symm) (R := F.featureEquiv ⁻¹' R) hsource)

end InfoGeometry.Topology
