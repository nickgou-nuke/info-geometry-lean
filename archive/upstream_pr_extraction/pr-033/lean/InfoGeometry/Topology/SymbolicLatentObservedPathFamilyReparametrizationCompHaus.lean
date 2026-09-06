import InfoGeometry.Topology.SymbolicLatentPathFamilyReparametrizationCompHaus
import InfoGeometry.Topology.SymbolicLatentPathFamilyTopCatColimitImageCompHaus
import InfoGeometry.Topology.SymbolicLatentObservedPathFamilyReparametrizationTopCat

/-!
# Compact-Hausdorff transport of observed path-family images

Reparametrization changes the range subtype even though it does not change
the observed feature values.  This owner packages the resulting identity-on-
values map between the two observed image subtypes as a `CompHaus` morphism.
-/

namespace InfoGeometry.Topology

open CategoryTheory

noncomputable section

variable {P X ι : Type} [TopologicalSpace P] [TopologicalSpace X]
  [Fintype ι] [CompactSpace P]

noncomputable def observedSymbolicLatentPathFamilyReparametrizationImageCompHausHom
    {X : Type} [TopologicalSpace X]
    (S : FiniteSymbolicLatentSystem X ι)
    (R : SymbolicLatentPathReparametrization)
    (H : SymbolicLatentPathFamily P X)
    (h_obs : Continuous (symbolicObservationMap S)) :
    observedSymbolicLatentPathFamilyImageCompHaus S
        (reparametrizeSymbolicLatentPathFamily R H) h_obs ⟶
      observedSymbolicLatentPathFamilyImageCompHaus S H h_obs := by
  letI : CompactSpace
      (observedSymbolicLatentPathFamilyImage S
        (reparametrizeSymbolicLatentPathFamily R H) h_obs) :=
    isCompact_iff_compactSpace.mp
      (isCompact_observedSymbolicLatentPathFamilyImage S
        (reparametrizeSymbolicLatentPathFamily R H) h_obs)
  letI : CompactSpace
      (observedSymbolicLatentPathFamilyImage S H h_obs) :=
    isCompact_iff_compactSpace.mp
      (isCompact_observedSymbolicLatentPathFamilyImage S H h_obs)
  dsimp [observedSymbolicLatentPathFamilyImageCompHaus]
  change CompHaus.of _ ⟶ CompHaus.of _
  exact ⟨TopCat.ofHom
    { toFun := observedSymbolicLatentPathFamilyReparametrizationImageMap
        S R H h_obs
      continuous_toFun := continuous_subtype_val.subtype_mk _ }⟩

theorem observedSymbolicLatentPathFamilyReparametrizationImageCompHausHom_forget
    {X : Type} [TopologicalSpace X]
    (S : FiniteSymbolicLatentSystem X ι)
    (R : SymbolicLatentPathReparametrization)
    (H : SymbolicLatentPathFamily P X)
    (h_obs : Continuous (symbolicObservationMap S)) :
    compHausToTop.map
      (observedSymbolicLatentPathFamilyReparametrizationImageCompHausHom
        S R H h_obs) =
      TopCat.ofHom
        { toFun := observedSymbolicLatentPathFamilyReparametrizationImageMap
            S R H h_obs
          continuous_toFun := continuous_subtype_val.subtype_mk _ } := by
  apply TopCat.hom_ext
  ext y
  rfl

theorem observedSymbolicLatentPathFamilyReparametrizationImageCompHausHom_inclusion
    {X : Type} [TopologicalSpace X]
    (S : FiniteSymbolicLatentSystem X ι)
    (R : SymbolicLatentPathReparametrization)
    (H : SymbolicLatentPathFamily P X)
    (h_obs : Continuous (symbolicObservationMap S)) :
    compHausToTop.map
      (observedSymbolicLatentPathFamilyReparametrizationImageCompHausHom
        S R H h_obs) ≫
        observedSymbolicLatentPathFamilyImageInclusionTopCatHom
          S H h_obs =
      observedSymbolicLatentPathFamilyImageInclusionTopCatHom
        S (reparametrizeSymbolicLatentPathFamily R H) h_obs := by
  apply TopCat.hom_ext
  ext y
  rfl

end
end InfoGeometry.Topology
