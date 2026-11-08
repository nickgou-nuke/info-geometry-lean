import InfoGeometry.Topology.SymbolicLatentObservedPathFamilyReparametrizationColimitCompHaus
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Topology.SymbolicLatentObservedPathFamilyReparametrizationCompHausLaws

/-!
# Colimit identity and composition laws for compact observed readouts

The corridor reparametrization acts on the `TopCat` colimit, while the
observed readout lands in a compact-Hausdorff image.  These laws package the
already-proved naturality square as identity and composition statements for
that mixed categorical interface.
-/

namespace InfoGeometry.Topology

open CategoryTheory
open SymbolicLatentPathFamilyTopCatColimitImageCompHaus

noncomputable section

variable {P X ι : Type} [TopologicalSpace P] [TopologicalSpace X]
  [Fintype ι] [CompactSpace P] [T2Space X]

theorem observedSymbolicLatentPathFamilyReparametrizationColimitCompHausReadout_identity
    (S : FiniteSymbolicLatentSystem X ι)
    (H : SymbolicLatentPathFamily P X)
    (h_obs : Continuous (symbolicObservationMap S)) :
    symbolicLatentPathFamilyReparametrizationColimitHom
        identitySymbolicLatentPathReparametrization ≫
        observedSymbolicLatentPathFamilyTopCatColimitImageCompHausReadout
          S H h_obs =
      observedSymbolicLatentPathFamilyTopCatColimitImageCompHausReadout
          S H h_obs ≫
        compHausToTop.map
          (observedSymbolicLatentPathFamilyReparametrizationImageCompHausHom
            S identitySymbolicLatentPathReparametrization H h_obs) := by
  have h := reparametrizeSymbolicLatentPathFamily_identity H
  cases h
  exact observedSymbolicLatentPathFamilyReparametrizationColimitCompHausReadout_natural
    S identitySymbolicLatentPathReparametrization H h_obs

theorem observedSymbolicLatentPathFamilyReparametrizationColimitCompHausReadout_comp
    (S : FiniteSymbolicLatentSystem X ι)
    (R T : SymbolicLatentPathReparametrization)
    (H : SymbolicLatentPathFamily P X)
    (h_obs : Continuous (symbolicObservationMap S)) :
    (symbolicLatentPathFamilyReparametrizationColimitHom R ≫
        symbolicLatentPathFamilyReparametrizationColimitHom T) ≫
        observedSymbolicLatentPathFamilyTopCatColimitImageCompHausReadout
          S H h_obs =
      observedSymbolicLatentPathFamilyTopCatColimitImageCompHausReadout
          S (reparametrizeSymbolicLatentPathFamily
              (composeSymbolicLatentPathReparametrization R T) H) h_obs ≫
        compHausToTop.map
          (observedSymbolicLatentPathFamilyReparametrizationImageCompHausHom
            S (composeSymbolicLatentPathReparametrization R T) H h_obs) := by
  rw [symbolicLatentPathFamilyReparametrizationColimitHom_comp]
  exact observedSymbolicLatentPathFamilyReparametrizationColimitCompHausReadout_natural
    S (composeSymbolicLatentPathReparametrization R T) H h_obs

end
end InfoGeometry.Topology
