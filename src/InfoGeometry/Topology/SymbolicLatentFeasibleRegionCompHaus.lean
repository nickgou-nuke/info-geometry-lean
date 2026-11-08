import InfoGeometry.Topology.SymbolicLatentObservedFamilyImageFeasibleTopCat
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Topology.Category.CompHaus.Basic

/-!
# Compact-Hausdorff feasible feature regions

The feasible-region owner already proves compactness of the finite product
region when every target is compact.  This file only lifts that subtype into
`CompHaus` and exposes the existing symbolic observation map through `TopCat`.
-/

noncomputable section

namespace InfoGeometry.Topology

open CategoryTheory

variable {X ι : Type} [TopologicalSpace X] [Fintype ι]

noncomputable def symbolicLatentFeasibleFeatureRegionCompHaus
    (targets : ι → Set ℝ)
    (hcompact : ∀ i, IsCompact (targets i)) : CompHaus := by
  letI : CompactSpace (symbolicLatentFeasibleFeatureRegion targets) :=
    isCompact_iff_compactSpace.mp
      (isCompact_symbolicLatentFeasibleFeatureRegion targets hcompact)
  exact CompHaus.of (symbolicLatentFeasibleFeatureRegion targets)

noncomputable def symbolicLatentFeasibleRegionObservationCompHausTopCatHom
    (S : FiniteSymbolicLatentSystem X ι)
    (targets : ι → Set ℝ)
    (hcompact : ∀ i, IsCompact (targets i)) :
    TopCat.of (feasibleLatentSubspace S targets) ⟶
      compHausToTop.obj
        (symbolicLatentFeasibleFeatureRegionCompHaus targets hcompact) := by
  change TopCat.of (feasibleLatentSubspace S targets) ⟶
    TopCat.of (symbolicLatentFeasibleFeatureRegion targets)
  exact symbolicLatentFeasibleRegionObservationTopCatHom S targets

theorem symbolicLatentFeasibleRegionObservationCompHausTopCatHom_apply
    (S : FiniteSymbolicLatentSystem X ι)
    (targets : ι → Set ℝ)
    (hcompact : ∀ i, IsCompact (targets i))
    (x : feasibleLatentSubspace S targets) :
    symbolicLatentFeasibleRegionObservationCompHausTopCatHom
        S targets hcompact x =
      symbolicLatentFeasibleRegionObservationTopCatHom S targets x :=
  rfl

end InfoGeometry.Topology
