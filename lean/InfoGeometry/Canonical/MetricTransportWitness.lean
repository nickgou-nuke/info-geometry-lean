import InfoGeometry.Canonical.OperatorProjectorMismatch
import Mathlib.Tactic.NoncommRing

/-!
# Metric transport witness

Theorem-safe transport layer:
- Drazin projector is similarity-natural (witnessed transport).
- Moore-Penrose projector is metric-natural (witnessed transport).
- Fixed-metric failures are recorded as an explicit tear term.

No automatic anomaly deletion and no automatic conformal-gravity closure claim.
-/

namespace InfoGeometry.Canonical.MetricTransportWitness

open InfoGeometry.Canonical.OperatorProjectorMismatch

variable {R : Type*} [Ring R]

/-- Abstract metric/adjoint package. `metricTransportLaw` is intentionally witness-level. -/
@[rep_depth transport]
structure MetricAdjointData where
  metric : R
  metricInv : R
  metric_leftInv : metricInv * metric = 1
  metric_rightInv : metric * metricInv = 1
  metricTransportLaw : Prop

/-- Moore--Penrose inverse data relative to a supplied metric package. -/
@[rep_depth transport]
structure MoorePenroseInverseG where
  metricData : MetricAdjointData (R := R)
  A : R
  B : R
  penrose₁ : A * B * A = A
  penrose₂ : B * A * B = B
  penrose₃_G : Prop
  penrose₄_G : Prop

/-- Similarity transport data between two projector pairs.

The metric-transport side is recorded as prose metadata, not as a proof-bearing
certificate field; the checked projector equations below are the Lean authority
available in this packet.
-/
@[rep_depth transport]
structure SimilarityTransportWitness (P P' : ProjectorPair R) where
  g : R
  gInv : R
  leftInv : gInv * g = 1
  rightInv : g * gInv = 1
  transportedMetricExplanation : String
  drazin_transport : P'.PD = g * P.PD * gInv
  moorePenrose_transport : P'.PMP = g * P.PMP * gInv

/-- Fixed-metric Moore--Penrose tear term (the non-equivariance defect). -/
def MPFixedTear (P P' : ProjectorPair R) (W : SimilarityTransportWitness P P') : R :=
  P'.PMP - W.g * P.PMP * W.gInv

/-- Drazin/MP mismatch in a chosen metric layer. -/
def mismatch_G (P : ProjectorPair R) : R :=
  ProjectorPair.mismatch P

/-- Transported metric witness restores Moore--Penrose covariance in witness form. -/
theorem transported_metric_restores_mp_covariance
    {P P' : ProjectorPair R}
    (W : SimilarityTransportWitness P P') :
    P'.PMP = W.g * P.PMP * W.gInv :=
  W.moorePenrose_transport

/-- Mismatch decomposition under fixed-metric transport:
`mismatch' = transported mismatch - MP fixed-metric tear`.
-/
theorem mismatch_transport_decomposition
    {P P' : ProjectorPair R}
    (W : SimilarityTransportWitness P P') :
    mismatch_G P' = W.g * mismatch_G P * W.gInv - MPFixedTear P P' W := by
  unfold mismatch_G MPFixedTear ProjectorPair.mismatch
    ProjectorPair.spectralProjector ProjectorPair.metricProjector
  rw [W.drazin_transport, W.moorePenrose_transport]
  noncomm_ring

/-- With transported metric witness, mismatch transports covariantly. -/
theorem transported_mismatch_covariant
    {P P' : ProjectorPair R}
    (W : SimilarityTransportWitness P P')
    (hTearZero : MPFixedTear P P' W = 0) :
    mismatch_G P' = W.g * mismatch_G P * W.gInv := by
  have h := mismatch_transport_decomposition (W := W)
  rw [hTearZero, sub_zero] at h
  exact h

/-- Formal compensator object: transported metric + projector transport obligations. -/
@[rep_depth transport]
structure MetricCompensatorWitness (P P' : ProjectorPair R) where
  transport : SimilarityTransportWitness P P'
  mp_transport : P'.PMP = transport.g * P.PMP * transport.gInv
  mismatch_transport : mismatch_G P' = transport.g * mismatch_G P * transport.gInv

/-- Local gauge/metric transport witness shell for geometric readout layers. -/
@[rep_depth transport]
structure LocalGaugeMetricTransportWitness where
  baseMetric : R
  connection : R
  covariantDerivative : Prop
  transportEquation : Prop
  mpEquivarianceLocal : Prop

end InfoGeometry.Canonical.MetricTransportWitness
