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
open InfoGeometry.Canonical.RindlerMobiusCantorFiniteBridge
open InfoGeometry.Canonical.CantorBoundaryFiniteReadout
open InfoGeometry.Canonical.CantorBoundaryReadoutBounds

/-- The canonical continuous readout from the projective limit to the unit interval. -/
def projectiveLimitUnitIntervalReadout (p : PrefixProjectiveLimit) : Set.Icc (0 : ℝ) 1 :=
  ⟨realBinaryReadout (toCantor p), realBinaryReadout_mem_unitInterval (toCantor p)⟩

theorem continuous_projectiveLimitUnitIntervalReadout :
    Continuous projectiveLimitUnitIntervalReadout := by
  change Continuous (fun p => (⟨realBinaryReadout (toCantor p), realBinaryReadout_mem_unitInterval (toCantor p)⟩ : Set.Icc (0 : ℝ) 1))
  exact continuous_projectiveLimit_readout.subtype_mk _

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

instance : MeasurableSpace (Set.Icc (0 : ℝ) 1) := borel (Set.Icc (0 : ℝ) 1)
instance : BorelSpace (Set.Icc (0 : ℝ) 1) := ⟨rfl⟩

def projectiveLimitUnitIntervalMeasure : Measure (Set.Icc (0 : ℝ) 1) :=
  Measure.map projectiveLimitUnitIntervalReadout projectiveLimitMeasure

instance projectiveLimitUnitIntervalMeasure_isProbabilityMeasure :
    IsProbabilityMeasure projectiveLimitUnitIntervalMeasure := by
  unfold projectiveLimitUnitIntervalMeasure
  exact Measure.isProbabilityMeasure_map
    continuous_projectiveLimitUnitIntervalReadout.measurable.aemeasurable

theorem topCat_readout_pushforward_is_probability :
    IsProbabilityMeasure
      (Measure.map
        (fun p : PrefixProjectiveLimit =>
          projectiveLimitUnitIntervalReadoutTopCatHom p)
        projectiveLimitMeasure) := by
  change IsProbabilityMeasure projectiveLimitUnitIntervalMeasure
  exact projectiveLimitUnitIntervalMeasure_isProbabilityMeasure

end InfoGeometry.Canonical.CantorProjectiveBernoulliMeasureTopCat
