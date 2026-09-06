import InfoGeometry.Topology.SymbolicLatentPathFamilyTopCatColimitImage
import InfoGeometry.Topology.SymbolicLatentPathFamilyImageCompHaus

namespace InfoGeometry.Topology.SymbolicLatentPathFamilyTopCatColimitImageCompHaus

open CategoryTheory CategoryTheory.Limits
open InfoGeometry.Topology
open InfoGeometry.Topology.SymbolicLatentPathFamilyTopCatColimit
open InfoGeometry.Topology.SymbolicLatentPathFamilyTopCatColimitImage

variable {P X ι : Type} [TopologicalSpace P] [TopologicalSpace X]
  [Fintype ι] [CompactSpace P] [T2Space X]

/-!
# Compact-Hausdorff target for the path-family colimit readout

The colimit readout is already constructed in `TopCat`.  This owner only
changes its codomain to the existing compact-Hausdorff packaging of the
observed path-family image and proves that the resulting morphism still
factors through the ambient symbolic path-family readout.
-/

noncomputable def observedSymbolicLatentPathFamilyTopCatColimitImageCompHausReadout
    (S : FiniteSymbolicLatentSystem X ι)
    (H : SymbolicLatentPathFamily P X)
    (h_obs : Continuous (symbolicObservationMap S)) :
    symbolicLatentPathFamilyTopCatColimit (P := P) ⟶
      compHausToTop.obj
        (observedSymbolicLatentPathFamilyImageCompHaus S H h_obs) := by
  change symbolicLatentPathFamilyTopCatColimit (P := P) ⟶
    TopCat.of (observedSymbolicLatentPathFamilyImage S H h_obs)
  exact observedSymbolicLatentPathFamilyTopCatColimitImageReadout S H h_obs

theorem observedSymbolicLatentPathFamilyTopCatColimitImageCompHausReadout_forget
    (S : FiniteSymbolicLatentSystem X ι)
    (H : SymbolicLatentPathFamily P X)
    (h_obs : Continuous (symbolicObservationMap S)) :
    observedSymbolicLatentPathFamilyTopCatColimitImageCompHausReadout
        S H h_obs =
      observedSymbolicLatentPathFamilyTopCatColimitImageReadout S H h_obs := by
  rfl

theorem observedSymbolicLatentPathFamilyTopCatColimitImageCompHausReadout_stage
    (S : FiniteSymbolicLatentSystem X ι)
    (H : SymbolicLatentPathFamily P X)
    (h_obs : Continuous (symbolicObservationMap S))
    (i : SpinorSpectrumTopCatColimit.SpinorStage) :
    colimit.ι (symbolicLatentPathFamilyTopCatDiagram (P := P)) i ≫
        observedSymbolicLatentPathFamilyTopCatColimitImageCompHausReadout
          S H h_obs =
      (observedSymbolicLatentPathFamilyImageCocone S H h_obs).ι.app i := by
  exact observedSymbolicLatentPathFamilyTopCatColimitImageReadout_stage S H h_obs i

theorem observedSymbolicLatentPathFamilyTopCatColimitImageCompHausReadout_factorization
    (S : FiniteSymbolicLatentSystem X ι)
    (H : SymbolicLatentPathFamily P X)
    (h_obs : Continuous (symbolicObservationMap S)) :
    observedSymbolicLatentPathFamilyTopCatColimitImageCompHausReadout S H h_obs ≫
        observedSymbolicLatentPathFamilyImageInclusionCompHausTopCatHom
          S H h_obs =
      symbolicLatentPathFamilyTopCatColimitReadout S H h_obs := by
  exact observedSymbolicLatentPathFamilyTopCatColimitImageReadout_factorization
    S H h_obs

end InfoGeometry.Topology.SymbolicLatentPathFamilyTopCatColimitImageCompHaus
