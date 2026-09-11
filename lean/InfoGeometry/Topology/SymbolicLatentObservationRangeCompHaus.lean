import InfoGeometry.Topology.SymbolicLatentObservationQuotientCompactTopCat
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Topology.Category.CompHaus.Basic

/-!
# Compact-Hausdorff packaging of symbolic observational ranges

The quotient/range owner already proves compactness and the quotient-map
property for compact carriers.  This file only lifts that existing range into
the native `CompHaus` category and keeps its TopCat readout available through
the standard faithful inclusion.
-/

noncomputable section

namespace InfoGeometry.Topology

open CategoryTheory

variable {X ι : Type} [TopologicalSpace X] [CompactSpace X] [Fintype ι]

noncomputable def symbolicObservationRangeCompHaus
    (S : FiniteSymbolicLatentSystem X ι) : CompHaus := by
  letI : CompactSpace (Set.range (symbolicObservationQuotientMap S)) :=
    isCompact_iff_compactSpace.mp
      (isCompact_symbolicObservationQuotient_range S)
  exact CompHaus.of (Set.range (symbolicObservationQuotientMap S))

noncomputable def symbolicObservationRangeCompHausTopCatHom
    (S : FiniteSymbolicLatentSystem X ι) :
    TopCat.of (_root_.Quotient (symbolicObservationalSetoid S)) ⟶
      compHausToTop.obj (symbolicObservationRangeCompHaus S) := by
  change TopCat.of (_root_.Quotient (symbolicObservationalSetoid S)) ⟶
    TopCat.of (Set.range (symbolicObservationQuotientMap S))
  exact symbolicObservationQuotientRangeCompactTopCatHom S

theorem symbolicObservationRangeCompHausTopCatHom_isIso
    (S : FiniteSymbolicLatentSystem X ι) :
    IsIso (symbolicObservationRangeCompHausTopCatHom S) := by
  change IsIso (symbolicObservationQuotientRangeCompactTopCatHom S)
  exact symbolicObservationQuotientRangeCompactTopCatHom_isIso S

end InfoGeometry.Topology
