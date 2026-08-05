import InfoGeometry.Canonical.CantorProjectiveBernoulliMeasure
import InfoGeometry.Canonical.CantorProjectiveBernoulliMeasureTopCat
import InfoGeometry.Canonical.CantorBoundaryReadoutIntervalTarget

/-!
# Pushforward of the Cantor readout measure to the unit interval

This bridge packages the already-proved projective-limit readout measure into a
small transport owner.  It does not prove a new pushforward theorem: the
measure and its probability normalization already exist in
`CantorProjectiveBernoulliMeasure`.
-/

noncomputable section

namespace InfoGeometry.Canonical.CantorReadoutMeasurePushforward

open MeasureTheory
open InfoGeometry.Canonical.CantorProjectiveBernoulliMeasure
open InfoGeometry.Canonical.CantorProjectiveBernoulliMeasureTopCat
open InfoGeometry.Canonical.CantorProjectiveLimit
open InfoGeometry.Canonical.CantorProjectiveLimit.PrefixProjectiveLimit
open InfoGeometry.Canonical.CantorBoundaryReadoutIntervalTarget

abbrev UnitInterval := CantorBoundaryReadoutIntervalTarget.UnitInterval

/-- The readout measure on the closed unit interval. -/
def continuumReadoutMeasure : Measure UnitInterval :=
  projectiveLimitUnitIntervalMeasure

theorem continuumReadoutMeasure_eq_topCat_pushforward :
    continuumReadoutMeasure =
      Measure.map
        projectiveLimitUnitIntervalReadout
        projectiveLimitMeasure := by
  rfl

/-- The readout measure is a probability measure. -/
instance continuumReadoutMeasure_isProbabilityMeasure :
    IsProbabilityMeasure continuumReadoutMeasure := by
  dsimp [continuumReadoutMeasure]
  infer_instance

/-- The unit interval has total mass one under the transported readout measure. -/
theorem continuumReadoutMeasure_univ :
    continuumReadoutMeasure Set.univ = 1 := by
  simp [continuumReadoutMeasure]

/-- The transported unit-interval measure is the pushforward of the readout. -/
theorem continuumReadoutMeasure_map_subtypeVal :
    Measure.map (fun x : UnitInterval => (x : ℝ)) continuumReadoutMeasure =
      projectiveLimitReadoutMeasure := by
  simpa [continuumReadoutMeasure] using
    projectiveLimitUnitIntervalMeasure_map_subtypeVal

end InfoGeometry.Canonical.CantorReadoutMeasurePushforward
