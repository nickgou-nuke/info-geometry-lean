import InfoGeometry.Canonical.WeylHomogeneousReadoutBridge
import InfoGeometry.OperatorAlgebra.ConnesSpatialDerivative
import InfoGeometry.SuperMetriplectic.OperatorKLBKM
import InfoGeometry.Meta.Architecture

/-!
# InfoGeometry.Canonical.BKMDriftMetric

Canonical Weyl-normalized BKM drift metric bridge.

This file is the mass/stiffness analogue of `WeylGWVolumeBridge`.

The owner lanes already present in the repository are:

* `OperatorAlgebra.ConnesSpatialDerivative`, which owns the abstract BKM metric
  datum and the constructive scalar positive-cone branch.
* `SuperMetriplectic.OperatorKLBKM`, which owns the operatorial KL/BKM Hessian
  packet and its nonnegativity/symmetry readbacks.

This canonical bridge adds only the Weyl normalization gate:

```text
weight 2 BKM drift intensity × inverse-weight 2 gauge = invariant mass/stiffness.
```

It does not assert that an arbitrary drift is a BKM gradient, that a metric is
the genuine infinite-dimensional Kubo-Mori form, or that a physical mass exists
without an explicit calibration predicate.
-/

namespace BKMDriftMetric

open InfoGeometry.Canonical.WeylHomogeneousReadoutBridge
open InfoGeometry.OperatorAlgebra.ConnesSpatialDerivative
open InfoGeometry.SuperMetriplectic

/--
Raw BKM drift metric carrier.

`driftIntensity` is the quadratic BKM/stiffness channel.  It is allowed to be
homogeneous of Weyl weight two.  `gaugeScale` is the inverse weight-two
normalizer.  `physicalMass` is the gauge-fixed scalar readout.
-/
@[rep_depth operator]
structure BKMDriftMetricCarrier
    (State : Type*) where
  scale : ℝ → State → State
  driftIntensity : State → ℝ
  gaugeScale : State → ℝ
  physicalMass : State → ℝ

/-- External predicate: physical mass/stiffness is drift intensity times gauge scale. -/
@[rep_depth operator]
def IsGaugeFixedBKMDriftMass
    {State : Type*}
    (M : BKMDriftMetricCarrier State) : Prop :=
  ∀ s : State, M.physicalMass s = M.driftIntensity s * M.gaugeScale s

/-- External predicate: the BKM drift intensity has Weyl weight two. -/
@[rep_depth operator]
def HasWeightTwoBKMDriftIntensity
    {State : Type*}
    (M : BKMDriftMetricCarrier State) : Prop :=
  ∀ (c : ℝ) (s : State),
    M.driftIntensity (M.scale c s) = c ^ 2 * M.driftIntensity s

/-- External predicate: the BKM gauge scale has inverse Weyl weight two. -/
@[rep_depth operator]
def HasInverseWeightTwoBKMGauge
    {State : Type*}
    (M : BKMDriftMetricCarrier State) : Prop :=
  ∀ (c : ℝ) (s : State),
    c ≠ 0 →
      M.gaugeScale (M.scale c s) = (c ^ 2)⁻¹ * M.gaugeScale s

/-- External predicate: the gauge scale is nonnegative on all states. -/
@[rep_depth operator]
def HasNonnegativeBKMGauge
    {State : Type*}
    (M : BKMDriftMetricCarrier State) : Prop :=
  ∀ s : State, 0 ≤ M.gaugeScale s

namespace BKMDriftMetricCarrier

variable {State : Type*}
variable (M : BKMDriftMetricCarrier State)

@[rep_depth operator]
theorem driftIntensity_apply (s : State) :
    M.driftIntensity s = M.driftIntensity s := rfl

@[rep_depth operator]
theorem gaugeScale_apply (s : State) :
    M.gaugeScale s = M.gaugeScale s := rfl

@[rep_depth operator]
theorem physicalMass_apply (s : State) :
    M.physicalMass s = M.physicalMass s := rfl

/--
Gauge-fixed BKM mass/stiffness is invariant under nonzero Weyl scaling.
-/
@[rep_depth operator]
theorem physicalMass_weylInvariant
    (hM : IsGaugeFixedBKMDriftMass M)
    (hI : HasWeightTwoBKMDriftIntensity M)
    (hG : HasInverseWeightTwoBKMGauge M)
    (c : ℝ) (s : State) (hc : c ≠ 0) :
    M.physicalMass (M.scale c s) = M.physicalMass s := by
  have hc2 : c ^ 2 ≠ 0 := pow_ne_zero 2 hc
  rw [hM (M.scale c s), hI c s, hG c s hc, hM s]
  field_simp [hc2]

/--
Gauge-fixed BKM mass/stiffness is nonnegative when the drift intensity and
gauge are nonnegative.
-/
@[rep_depth operator]
theorem physicalMass_nonnegative
    (hM : IsGaugeFixedBKMDriftMass M)
    (hI : ∀ s : State, 0 ≤ M.driftIntensity s)
    (hG : HasNonnegativeBKMGauge M)
    (s : State) :
    0 ≤ M.physicalMass s := by
  rw [hM s]
  exact mul_nonneg (hI s) (hG s)

end BKMDriftMetricCarrier

/-! ## Fusion with the existing Connes/BKM metric owner lane -/

/--
Canonical socket connecting an existing `BKMMetricDatum` to a Weyl-normalized
mass/stiffness readout.

The equality between `metric φ X X` and `driftIntensity` is an external
calibration predicate below.
-/
@[rep_depth operator]
structure ConnesBKMDriftFusion
    (Weight Tangent State : Type*)
    [AddCommGroup Tangent] [Module ℝ Tangent] where
  bkm : BKMMetricDatum Weight Tangent
  stateWeight : State → Weight
  tangentDrift : State → Tangent
  metric : BKMDriftMetricCarrier State

/--
External predicate: the carrier's drift intensity is the diagonal BKM metric of
the supplied Connes/spatial-derivative datum.
-/
@[rep_depth operator]
def DriftIntensityCalibratesConnesBKM
    {Weight Tangent State : Type*}
    [AddCommGroup Tangent] [Module ℝ Tangent]
    (F : ConnesBKMDriftFusion Weight Tangent State) : Prop :=
  ∀ s : State,
    F.metric.driftIntensity s =
      F.bkm.metric (F.stateWeight s) (F.tangentDrift s) (F.tangentDrift s)

namespace ConnesBKMDriftFusion

variable {Weight Tangent State : Type*}
variable [AddCommGroup Tangent] [Module ℝ Tangent]
variable (F : ConnesBKMDriftFusion Weight Tangent State)

@[rep_depth operator]
theorem bkm_apply :
    F.bkm = F.bkm := rfl

@[rep_depth operator]
theorem metric_apply :
    F.metric = F.metric := rfl

/--
The calibrated BKM drift intensity is nonnegative by the imported BKM metric
owner theorem.
-/
@[rep_depth operator]
theorem driftIntensity_nonnegative
    (hcal : DriftIntensityCalibratesConnesBKM F)
    (s : State) :
    0 ≤ F.metric.driftIntensity s := by
  rw [hcal s]
  exact F.bkm.nonnegative_apply (F.stateWeight s) (F.tangentDrift s)

/--
The calibrated physical BKM mass/stiffness is nonnegative after gauge fixing.
-/
@[rep_depth operator]
theorem physicalMass_nonnegative
    (hcal : DriftIntensityCalibratesConnesBKM F)
    (hM : IsGaugeFixedBKMDriftMass F.metric)
    (hG : HasNonnegativeBKMGauge F.metric)
    (s : State) :
    0 ≤ F.metric.physicalMass s :=
  F.metric.physicalMass_nonnegative hM
    (fun x => F.driftIntensity_nonnegative hcal x) hG s

end ConnesBKMDriftFusion

/-! ## Fusion with the existing operator KL/BKM Hessian owner lane -/

/--
Canonical socket connecting the operatorial KL/BKM Hessian packet to a
Weyl-normalized drift mass/stiffness readout.
-/
@[rep_depth operator]
structure OperatorBKMDriftFusion
    (Op State : Type*) where
  bkmHessian : OperatorBKMHessianPacket Op
  driftGenerator : State → Op
  metric : BKMDriftMetricCarrier State

/--
External predicate: the carrier's drift intensity is the diagonal BKM Hessian
of the supplied operator generator.
-/
@[rep_depth operator]
def DriftIntensityCalibratesOperatorBKM
    {Op State : Type*}
    (F : OperatorBKMDriftFusion Op State) : Prop :=
  ∀ s : State,
    F.metric.driftIntensity s =
      F.bkmHessian.bkm (F.driftGenerator s) (F.driftGenerator s)

namespace OperatorBKMDriftFusion

variable {Op State : Type*}
variable (F : OperatorBKMDriftFusion Op State)

@[rep_depth operator]
theorem bkmHessian_apply :
    F.bkmHessian = F.bkmHessian := rfl

@[rep_depth operator]
theorem metric_apply :
    F.metric = F.metric := rfl

/--
The calibrated operator BKM drift intensity is nonnegative by the imported
operator KL/BKM owner theorem.
-/
@[rep_depth operator]
theorem driftIntensity_nonnegative
    (hcal : DriftIntensityCalibratesOperatorBKM F)
    (s : State) :
    0 ≤ F.metric.driftIntensity s := by
  rw [hcal s]
  exact F.bkmHessian.bkm_nonneg (F.driftGenerator s)

/--
The operatorial Hessian readout equals the calibrated BKM intensity.
-/
@[rep_depth operator]
theorem hessian_drift_eq_intensity
    (hcal : DriftIntensityCalibratesOperatorBKM F)
    (s : State) :
    F.bkmHessian.hessian (F.driftGenerator s) (F.driftGenerator s) =
      F.metric.driftIntensity s := by
  rw [F.bkmHessian.hessian_eq_bkm_form, hcal s]

/--
The calibrated physical operator BKM mass/stiffness is nonnegative after gauge
fixing.
-/
@[rep_depth operator]
theorem physicalMass_nonnegative
    (hcal : DriftIntensityCalibratesOperatorBKM F)
    (hM : IsGaugeFixedBKMDriftMass F.metric)
    (hG : HasNonnegativeBKMGauge F.metric)
    (s : State) :
    0 ≤ F.metric.physicalMass s :=
  F.metric.physicalMass_nonnegative hM
    (fun x => F.driftIntensity_nonnegative hcal x) hG s

end OperatorBKMDriftFusion

end BKMDriftMetric
