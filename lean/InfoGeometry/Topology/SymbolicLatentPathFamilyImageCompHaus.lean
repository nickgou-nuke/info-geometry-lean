import InfoGeometry.Topology.SymbolicLatentObservedFamilyImageTopCat
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Topology.Category.CompHaus.Basic

/-!
# Compact-Hausdorff packaging of observed symbolic path-family images

The observed image owner already proves compactness for compact parameter
spaces.  This file only packages that existing subtype in `CompHaus` and
exposes the native image evaluation morphism through the faithful `TopCat`
inclusion.
-/

noncomputable section

namespace InfoGeometry.Topology

open CategoryTheory

variable {P X ι : Type} [TopologicalSpace P] [TopologicalSpace X]
  [CompactSpace P] [Fintype ι]

noncomputable def observedSymbolicLatentPathFamilyImageCompHaus
    (S : FiniteSymbolicLatentSystem X ι)
    (H : SymbolicLatentPathFamily P X)
    (h_obs : Continuous (symbolicObservationMap S)) : CompHaus := by
  letI : CompactSpace (observedSymbolicLatentPathFamilyImage S H h_obs) :=
    isCompact_iff_compactSpace.mp
      (isCompact_observedSymbolicLatentPathFamilyImage S H h_obs)
  exact CompHaus.of (observedSymbolicLatentPathFamilyImage S H h_obs)

noncomputable def observedSymbolicLatentPathFamilyImageEvaluationCompHausTopCatHom
    (S : FiniteSymbolicLatentSystem X ι)
    (H : SymbolicLatentPathFamily P X)
    (h_obs : Continuous (symbolicObservationMap S)) :
    TopCat.of (P × SymbolicPathDomain) ⟶
      compHausToTop.obj
        (observedSymbolicLatentPathFamilyImageCompHaus S H h_obs) := by
  change TopCat.of (P × SymbolicPathDomain) ⟶
    TopCat.of (observedSymbolicLatentPathFamilyImage S H h_obs)
  exact observedSymbolicLatentPathFamilyImageEvaluationTopCatHom S H h_obs

noncomputable def observedSymbolicLatentPathFamilyImageInclusionCompHausTopCatHom
    (S : FiniteSymbolicLatentSystem X ι)
    (H : SymbolicLatentPathFamily P X)
    (h_obs : Continuous (symbolicObservationMap S)) :
    compHausToTop.obj
        (observedSymbolicLatentPathFamilyImageCompHaus S H h_obs) ⟶
      TopCat.of (SymbolicFeatureSpace ι) := by
  change TopCat.of (observedSymbolicLatentPathFamilyImage S H h_obs) ⟶
    TopCat.of (SymbolicFeatureSpace ι)
  exact observedSymbolicLatentPathFamilyImageInclusionTopCatHom S H h_obs

theorem observedSymbolicLatentPathFamilyImageCompHaus_factorization
    (S : FiniteSymbolicLatentSystem X ι)
    (H : SymbolicLatentPathFamily P X)
    (h_obs : Continuous (symbolicObservationMap S)) :
    observedSymbolicLatentPathFamilyImageEvaluationCompHausTopCatHom S H h_obs ≫
        observedSymbolicLatentPathFamilyImageInclusionCompHausTopCatHom S H h_obs =
      observedSymbolicLatentPathFamilyTopCatHom S H h_obs := by
  exact observedSymbolicLatentPathFamilyImage_evaluation_factorization S H h_obs

end InfoGeometry.Topology
