import InfoGeometry.Topology.TripotentFiveGradeSymbolicLatent
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Topology.SymbolicLatentObservationRangeCompHaus
import Mathlib.Topology.Category.CompHaus.Basic

/-!
# Compact-Hausdorff packaging for the five-grade symbolic latent system

This file keeps the five-grade symbolic-latent layer purely topological: the
one-hot observation map is continuous, its image is compact, and the image can
therefore be packaged as a native `CompHaus` object.
-/

noncomputable section

namespace InfoGeometry.Topology.TripotentFiveGradeSymbolicLatentCompHaus

open CategoryTheory
open InfoGeometry.Topology
open InfoGeometry.Topology.TripotentFiveGradeSymbolicLatent
open InfoGeometry.Physics.Algebra

local instance : TopologicalSpace InfoGeometry.Physics.Algebra.FiveGrade := ⊥
local instance : DiscreteTopology InfoGeometry.Physics.Algebra.FiveGrade :=
  discreteTopology_bot _
local instance : CompactSpace InfoGeometry.Physics.Algebra.FiveGrade := by
  infer_instance

theorem fiveGradeObservationalSetoid_iff_eq
    (x y : InfoGeometry.Physics.Algebra.FiveGrade) :
    @Setoid.r InfoGeometry.Physics.Algebra.FiveGrade
      (symbolicObservationalSetoid fiveGradeSystem) x y ↔
      x = y := by
  constructor
  · intro h
    exact InfoGeometry.Topology.TripotentFiveGradeSymbolicLatent.fiveGradeObservationMap_injective h
  · intro h
    subst h
    rfl

theorem fiveGradeObservationRange_isCompact :
    IsCompact (Set.range (symbolicObservationMap fiveGradeSystem)) := by
  simpa using (isCompact_range (continuous_symbolicObservationMap fiveGradeSystem))

noncomputable def fiveGradeObservationRangeCompHaus : CompHaus := by
  letI : CompactSpace (Set.range (symbolicObservationMap fiveGradeSystem)) :=
    isCompact_iff_compactSpace.mp fiveGradeObservationRange_isCompact
  exact CompHaus.of (Set.range (symbolicObservationMap fiveGradeSystem))

end InfoGeometry.Topology.TripotentFiveGradeSymbolicLatentCompHaus
