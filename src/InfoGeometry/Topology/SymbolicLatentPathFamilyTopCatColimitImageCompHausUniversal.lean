import InfoGeometry.Topology.SymbolicLatentPathFamilyTopCatColimitImageCompHaus
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Universal property of the compact-Hausdorff target readout

The colimit itself remains a `TopCat` object.  This owner records the
uniqueness of its readout into the existing compact-Hausdorff observed image,
using the already proved `TopCat` universal property after changing only the
codomain presentation.
-/

namespace InfoGeometry.Topology.SymbolicLatentPathFamilyTopCatColimitImageCompHaus

open CategoryTheory CategoryTheory.Limits
open InfoGeometry.Topology
open InfoGeometry.Topology.SymbolicLatentPathFamilyTopCatColimit
open InfoGeometry.Topology.SymbolicLatentPathFamilyTopCatColimitImage

variable {P X ι : Type} [TopologicalSpace P] [TopologicalSpace X]
  [Fintype ι] [CompactSpace P] [T2Space X]

theorem observedSymbolicLatentPathFamilyTopCatColimitImageCompHausReadout_unique
    (S : FiniteSymbolicLatentSystem X ι)
    (H : SymbolicLatentPathFamily P X)
    (h_obs : Continuous (symbolicObservationMap S))
    {u : symbolicLatentPathFamilyTopCatColimit (P := P) ⟶
      compHausToTop.obj
        (observedSymbolicLatentPathFamilyImageCompHaus S H h_obs)}
    (hu : u ≫ observedSymbolicLatentPathFamilyImageInclusionCompHausTopCatHom
        S H h_obs =
      symbolicLatentPathFamilyTopCatColimitReadout S H h_obs) :
    u = observedSymbolicLatentPathFamilyTopCatColimitImageCompHausReadout
      S H h_obs := by
  change u ≫ observedSymbolicLatentPathFamilyImageInclusionTopCatHom
      S H h_obs = symbolicLatentPathFamilyTopCatColimitReadout S H h_obs at hu
  change u = observedSymbolicLatentPathFamilyTopCatColimitImageReadout
      S H h_obs
  exact observedSymbolicLatentPathFamilyTopCatColimitImageReadout_unique
    S H h_obs hu

end InfoGeometry.Topology.SymbolicLatentPathFamilyTopCatColimitImageCompHaus
