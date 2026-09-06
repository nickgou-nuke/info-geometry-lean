import Mathlib.Topology.Category.TopCat.Basic
import InfoGeometry.Canonical.CantorProjectiveBernoulliMeasure

/-!
# TopCat surface for the projective Bernoulli readout

The measure owner proves probability normalization and interval support.  This
file exposes its already-continuous readout as a `TopCat` morphism, keeping the
measure-theoretic and categorical layers separate.
-/

noncomputable section

namespace InfoGeometry.Canonical.CantorProjectiveBernoulliMeasureTopCat

open MeasureTheory
open InfoGeometry.Canonical.CantorProjectiveBernoulliMeasure
open InfoGeometry.Canonical.CantorProjectiveLimit
open InfoGeometry.Canonical.CantorProjectiveLimit.PrefixProjectiveLimit

def projectiveLimitUnitIntervalReadoutTopCatHom :
    TopCat.of PrefixProjectiveLimit ⟶
      TopCat.of (Set.Icc (0 : ℝ) 1) :=
  TopCat.ofHom
    { toFun := projectiveLimitUnitIntervalReadout
      continuous_toFun := continuous_projectiveLimitUnitIntervalReadout }

@[simp] theorem projectiveLimitUnitIntervalReadoutTopCatHom_apply
    (p : PrefixProjectiveLimit) :
    projectiveLimitUnitIntervalReadoutTopCatHom p =
      projectiveLimitUnitIntervalReadout p :=
  rfl

theorem projectiveLimitUnitIntervalReadoutTopCatHom_continuous :
    Continuous projectiveLimitUnitIntervalReadout :=
  continuous_projectiveLimitUnitIntervalReadout

theorem topCat_readout_pushforward_is_probability :
    IsProbabilityMeasure
      (Measure.map
        (fun p : PrefixProjectiveLimit =>
          projectiveLimitUnitIntervalReadoutTopCatHom p)
        projectiveLimitMeasure) := by
  change IsProbabilityMeasure projectiveLimitUnitIntervalMeasure
  exact projectiveLimitUnitIntervalMeasure_isProbabilityMeasure

end InfoGeometry.Canonical.CantorProjectiveBernoulliMeasureTopCat
