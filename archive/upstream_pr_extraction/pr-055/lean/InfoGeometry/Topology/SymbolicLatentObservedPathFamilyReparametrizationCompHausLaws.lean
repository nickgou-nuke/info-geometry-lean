import InfoGeometry.Topology.SymbolicLatentObservedPathFamilyReparametrizationCompHaus

/-!
# Identity and composition laws for observed reparametrization in `CompHaus`

The canonical observed-image map is owned by the TopCat reparametrization
module and lifted to `CompHaus` by the adjacent compact-Hausdorff owner.
This file records only the categorical identity and composition laws for that
lift; it does not introduce another map or another compactness argument.
-/

namespace InfoGeometry.Topology

open CategoryTheory

noncomputable section

variable {P X ι : Type} [TopologicalSpace P] [TopologicalSpace X]
  [Fintype ι] [CompactSpace P] [T2Space X]

theorem observedSymbolicLatentPathFamilyReparametrizationImageCompHausHom_identity
    (S : FiniteSymbolicLatentSystem X ι)
    (H : SymbolicLatentPathFamily P X)
    (h_obs : Continuous (symbolicObservationMap S)) :
    observedSymbolicLatentPathFamilyReparametrizationImageCompHausHom
        S identitySymbolicLatentPathReparametrization H h_obs =
      𝟙 (observedSymbolicLatentPathFamilyImageCompHaus S H h_obs) := by
  have h := reparametrizeSymbolicLatentPathFamily_identity H
  cases h
  apply ConcreteCategory.hom_ext
  intro x
  rfl

theorem observedSymbolicLatentPathFamilyReparametrizationImageCompHausHom_comp
    (S : FiniteSymbolicLatentSystem X ι)
    (R T : SymbolicLatentPathReparametrization)
    (H : SymbolicLatentPathFamily P X)
    (h_obs : Continuous (symbolicObservationMap S)) :
    observedSymbolicLatentPathFamilyReparametrizationImageCompHausHom
        S R (reparametrizeSymbolicLatentPathFamily T H) h_obs ≫
      observedSymbolicLatentPathFamilyReparametrizationImageCompHausHom
        S T H h_obs =
      observedSymbolicLatentPathFamilyReparametrizationImageCompHausHom
        S (composeSymbolicLatentPathReparametrization R T) H h_obs := by
  have h := reparametrizeSymbolicLatentPathFamily_comp R T H
  cases h
  apply ConcreteCategory.hom_ext
  intro x
  rfl

end
end InfoGeometry.Topology
