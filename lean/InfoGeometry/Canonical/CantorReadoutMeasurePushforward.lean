import InfoGeometry.Canonical.CantorProjectiveBernoulliMeasure
import InfoGeometry.Canonical.CantorProjectiveBernoulliMeasureTopCat
import InfoGeometry.Canonical.CantorBoundaryReadoutIntervalTarget

/-!
# Pushforward of the Cantor readout measure to the unit interval

The Bernoulli measure owner is the native source of the measure, probability
instance, and pushforward identity.  This file records their combined
consequence without introducing a second measure definition.
-/

noncomputable section

namespace InfoGeometry.Canonical.CantorReadoutMeasurePushforward

open MeasureTheory
open InfoGeometry.Canonical.CantorProjectiveBernoulliMeasure
open InfoGeometry.Canonical.CantorProjectiveBernoulliMeasureTopCat
open InfoGeometry.Canonical.CantorProjectiveLimit
open InfoGeometry.Canonical.CantorProjectiveLimit.PrefixProjectiveLimit
open InfoGeometry.Canonical.CantorBoundaryReadoutIntervalTarget

theorem projectiveLimitUnitIntervalMeasure_map_subtypeVal :
    Measure.map Subtype.val projectiveLimitUnitIntervalMeasure =
      projectiveLimitReadoutMeasure := by
  dsimp [projectiveLimitUnitIntervalMeasure, projectiveLimitReadoutMeasure]
  rw [Measure.map_map continuous_subtype_val.measurable
    continuous_projectiveLimitUnitIntervalReadout.measurable]
  rfl

theorem projectiveLimitReadoutMeasure_isProbabilityMeasure :
    IsProbabilityMeasure projectiveLimitReadoutMeasure := by
  rw [← projectiveLimitUnitIntervalMeasure_map_subtypeVal]
  exact Measure.isProbabilityMeasure_map continuous_subtype_val.aemeasurable

end InfoGeometry.Canonical.CantorReadoutMeasurePushforward
