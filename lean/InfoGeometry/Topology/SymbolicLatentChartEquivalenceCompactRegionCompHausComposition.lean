import InfoGeometry.Topology.SymbolicLatentChartEquivalenceCompactRegionCompHaus
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Composition of compact chart-equivalence transports

The compact-region `CompHaus` isomorphism is functorial under composition of
chart equivalences.  The intermediate compactness property is transported by
the first equivalence; no new compactness or gluing ax!om is introduced.
-/

noncomputable section

namespace InfoGeometry.Topology

open CategoryTheory

theorem SymbolicLatentChartEquivalence.latentFeatureRegionCompHausIso_comp
    {X Y Z : Type} [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace Z]
    {ι : Type} [Fintype ι] [T2Space X] [T2Space Y] [T2Space Z]
    {C : SymbolicLatentChart X ι}
    {D : SymbolicLatentChart Y ι}
    {E : SymbolicLatentChart Z ι}
    (G : SymbolicLatentChartEquivalence D E)
    (F : SymbolicLatentChartEquivalence C D)
    (R : Set (SymbolicFeatureSpace ι))
    (hsource : IsCompact
      (Set.univ : Set
        {x // x ∈ latentFeatureRegion C ((G.comp F).featureEquiv ⁻¹' R)})) :
    ((G.comp F).latentFeatureRegionCompHausIso R hsource).hom =
      (F.latentFeatureRegionCompHausIso (G.featureEquiv ⁻¹' R) hsource).hom ≫
        (G.latentFeatureRegionCompHausIso R
          (F.latentFeatureRegion_compact_transport
            (G.featureEquiv ⁻¹' R) hsource)).hom := by
  apply ConcreteCategory.hom_ext
  intro x
  rfl

theorem SymbolicLatentChartEquivalence.latentFeatureRegionCompHausIso_inv_comp
    {X Y Z : Type} [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace Z]
    {ι : Type} [Fintype ι] [T2Space X] [T2Space Y] [T2Space Z]
    {C : SymbolicLatentChart X ι}
    {D : SymbolicLatentChart Y ι}
    {E : SymbolicLatentChart Z ι}
    (G : SymbolicLatentChartEquivalence D E)
    (F : SymbolicLatentChartEquivalence C D)
    (R : Set (SymbolicFeatureSpace ι))
    (hsource : IsCompact
      (Set.univ : Set
        {x // x ∈ latentFeatureRegion C ((G.comp F).featureEquiv ⁻¹' R)})) :
    ((G.comp F).latentFeatureRegionCompHausIso R hsource).inv =
      (G.latentFeatureRegionCompHausIso R
          (F.latentFeatureRegion_compact_transport
            (G.featureEquiv ⁻¹' R) hsource)).inv ≫
        (F.latentFeatureRegionCompHausIso (G.featureEquiv ⁻¹' R) hsource).inv := by
  apply ConcreteCategory.hom_ext
  intro x
  rfl

end InfoGeometry.Topology
