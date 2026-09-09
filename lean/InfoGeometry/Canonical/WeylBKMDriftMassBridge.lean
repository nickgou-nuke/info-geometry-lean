import InfoGeometry.Canonical.BKMDriftMetric
import InfoGeometry.Canonical.DrazinSupercharge
import InfoGeometry.Meta.Architecture

/-!
# InfoGeometry.Canonical.WeylBKMDriftMassBridge

Named mass layer for Weyl-normalized BKM drift readouts.

`BKMDriftMetric` already owns the core invariant product:

```text
drift intensity × inverse projective gauge = invariant stiffness.
```

This file adds the modular mass unit explicitly:

```text
physical mass = modular mass unit × drift intensity × inverse projective gauge.
```

The first theorem proves projective invariance when the modular mass unit is
itself projectively invariant.  Geometric Weyl dimension, such as an extra
`exp (-φ)` mass factor, is deliberately separated as a later calibration.

The Drazin supercharge layer is imported as the intended source of modular-twin
drift data; this file does not rederive `Q`, `Q²`, or a BKM score map.
-/

namespace InfoGeometry.Canonical.WeylBKMDriftMassBridge

open InfoGeometry.Canonical.BKMDriftMetric

/--
Weyl/BKM drift mass carrier.

`driftIntensity` is the positive homogeneous BKM norm-like channel.
`gaugeScale` cancels the projective representative scale.
`modularMassUnit` supplies the calibrated mass unit.
`weylParameter` is only a named geometric Weyl-depth channel here; no theorem
uses it unless an explicit geometric calibration predicate is supplied.
-/
@[rep_depth operator]
structure WeylBKMDriftMassCarrier
    (State : Type*) where
  driftIntensity : State → ℝ
  gaugeScale : State → ℝ
  modularMassUnit : State → ℝ
  weylParameter : State → ℝ
  physicalMass : State → ℝ

/-- External predicate: BKM drift intensity has projective/Weyl weight two. -/
@[rep_depth operator]
def HasWeightTwoDriftIntensity
    {State : Type*}
    (B : WeylBKMDriftMassCarrier State)
    (scale : ℝ → State → State) : Prop :=
  ∀ (c : ℝ) (s : State),
    c ≠ 0 →
      B.driftIntensity (scale c s) = c ^ 2 * B.driftIntensity s

/-- External predicate: mass gauge has inverse projective/Weyl weight two. -/
@[rep_depth operator]
def HasInverseWeightTwoMassGauge
    {State : Type*}
    (B : WeylBKMDriftMassCarrier State)
    (scale : ℝ → State → State) : Prop :=
  ∀ (c : ℝ) (s : State),
    c ≠ 0 →
      B.gaugeScale (scale c s) = (c ^ 2)⁻¹ * B.gaugeScale s

/-- External predicate: modular mass unit is invariant under projective representative scaling. -/
@[rep_depth operator]
def HasInvariantModularMassUnit
    {State : Type*}
    (B : WeylBKMDriftMassCarrier State)
    (scale : ℝ → State → State) : Prop :=
  ∀ (c : ℝ) (s : State),
    c ≠ 0 →
      B.modularMassUnit (scale c s) = B.modularMassUnit s

/-- External predicate: physical mass is the gauge-fixed BKM drift product. -/
@[rep_depth operator]
def IsGaugeFixedMass
    {State : Type*}
    (B : WeylBKMDriftMassCarrier State) : Prop :=
  ∀ s : State,
    B.physicalMass s =
      B.modularMassUnit s * B.driftIntensity s * B.gaugeScale s

/-- External predicate: the drift intensity is nonnegative. -/
@[rep_depth operator]
def HasNonnegativeDriftIntensity
    {State : Type*}
    (B : WeylBKMDriftMassCarrier State) : Prop :=
  ∀ s : State, 0 ≤ B.driftIntensity s

/-- External predicate: the mass gauge is nonnegative. -/
@[rep_depth operator]
def HasNonnegativeMassGauge
    {State : Type*}
    (B : WeylBKMDriftMassCarrier State) : Prop :=
  ∀ s : State, 0 ≤ B.gaugeScale s

/-- External predicate: the modular mass unit is nonnegative. -/
@[rep_depth operator]
def HasNonnegativeModularMassUnit
    {State : Type*}
    (B : WeylBKMDriftMassCarrier State) : Prop :=
  ∀ s : State, 0 ≤ B.modularMassUnit s

namespace WeylBKMDriftMassCarrier

variable {State : Type*}
variable (B : WeylBKMDriftMassCarrier State)

/--
Projective invariance of Weyl-gauge-fixed BKM drift mass.

This is the mass analogue of `WeylGWVolumeCarrier.physicalVolume_weylInvariant`.
-/
@[rep_depth operator]
theorem physicalMass_projectiveInvariant
    (scale : ℝ → State → State)
    (hI : HasWeightTwoDriftIntensity B scale)
    (hG : HasInverseWeightTwoMassGauge B scale)
    (hμ : HasInvariantModularMassUnit B scale)
    (hM : IsGaugeFixedMass B)
    (c : ℝ) (s : State) (hc : c ≠ 0) :
    B.physicalMass (scale c s) = B.physicalMass s := by
  have hc2 : c ^ 2 ≠ 0 := pow_ne_zero 2 hc
  rw [hM (scale c s), hμ c s hc, hI c s hc, hG c s hc, hM s]
  field_simp [hc2]

/-- Gauge-fixed BKM drift mass is nonnegative from nonnegative factors. -/
@[rep_depth operator]
theorem physicalMass_nonnegative
    (hM : IsGaugeFixedMass B)
    (hμ : HasNonnegativeModularMassUnit B)
    (hI : HasNonnegativeDriftIntensity B)
    (hG : HasNonnegativeMassGauge B)
    (s : State) :
    0 ≤ B.physicalMass s := by
  rw [hM s]
  exact mul_nonneg (mul_nonneg (hμ s) (hI s)) (hG s)

end WeylBKMDriftMassCarrier

/-! ## Compatibility with the existing `BKMDriftMetric` carrier -/

/--
Fusion socket from the earlier metric/stiffness carrier to the named modular
mass carrier.
-/
@[rep_depth operator]
structure BKMDriftMetricMassFusion
    (State : Type*) where
  metric : BKMDriftMetricCarrier State
  mass : WeylBKMDriftMassCarrier State

/-- External predicate: mass drift/gauge channels are inherited from the metric carrier. -/
@[rep_depth operator]
def MassChannelsCalibrateBKMDriftMetric
    {State : Type*}
    (F : BKMDriftMetricMassFusion State) : Prop :=
  (∀ s : State, F.mass.driftIntensity s = F.metric.driftIntensity s) ∧
    (∀ s : State, F.mass.gaugeScale s = F.metric.gaugeScale s)

namespace BKMDriftMetricMassFusion

variable {State : Type*}
variable (F : BKMDriftMetricMassFusion State)

/-- Inherited drift intensity calibration. -/
@[rep_depth operator]
theorem driftIntensity_eq_metric
    (hcal : MassChannelsCalibrateBKMDriftMetric F)
    (s : State) :
    F.mass.driftIntensity s = F.metric.driftIntensity s :=
  hcal.1 s

/-- Inherited mass gauge calibration. -/
@[rep_depth operator]
theorem gaugeScale_eq_metric
    (hcal : MassChannelsCalibrateBKMDriftMetric F)
    (s : State) :
    F.mass.gaugeScale s = F.metric.gaugeScale s :=
  hcal.2 s

end BKMDriftMetricMassFusion

end InfoGeometry.Canonical.WeylBKMDriftMassBridge
