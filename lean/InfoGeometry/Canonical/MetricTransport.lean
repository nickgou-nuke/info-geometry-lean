import InfoGeometry.Canonical.OperatorProjectorMismatch
import Mathlib.Tactic.NoncommRing

/-!
# Metric transport

Theorem-safe transport layer:
- Drazin projector is similarity-natural under supplied transport equations.
- Moore-Penrose projector is metric-natural under supplied transport equations.
- Fixed-metric failures are recorded as an explicit tear term.

No automatic anomaly deletion and no automatic conformal-gravity closure claim.
-/

namespace MetricTransport

open OperatorProjectorMismatch
open OperatorProjectorMismatch.ProjectorPair

variable {R : Type*} [Ring R]

/-- Similarity transport data between two projector pairs.

The checked projector equations below are the Lean authority available in this
transport object.
-/
@[rep_depth transport]
structure SimilarityTransport (P P' : ProjectorPair R) where
  g : R
  gInv : R
  leftInv : gInv * g = 1
  rightInv : g * gInv = 1
  drazin_transport : P'.PD = g * P.PD * gInv
  moorePenrose_transport : P'.PMP = g * P.PMP * gInv

/-- Fixed-metric Moore--Penrose tear term (the non-equivariance defect). -/
def MPFixedTear (P P' : ProjectorPair R) (W : SimilarityTransport P P') : R :=
  P'.PMP - W.g * P.PMP * W.gInv

/-- Drazin/MP mismatch in a chosen metric layer. -/
def mismatch_G (P : ProjectorPair R) : R :=
  ProjectorPair.mismatch P

/-- Transported metric restores Moore--Penrose covariance. -/
theorem transported_metric_restores_mp_covariance
    {P P' : ProjectorPair R}
    (W : SimilarityTransport P P') :
    P'.PMP = W.g * P.PMP * W.gInv :=
  W.moorePenrose_transport

/-- Mismatch decomposition under fixed-metric transport:
`mismatch' = transported mismatch - MP fixed-metric tear`.
-/
theorem mismatch_transport_decomposition
    {P P' : ProjectorPair R}
    (W : SimilarityTransport P P') :
    mismatch_G P' = W.g * mismatch_G P * W.gInv - MPFixedTear P P' W := by
  unfold mismatch_G MPFixedTear ProjectorPair.mismatch
    ProjectorPair.spectralProjector ProjectorPair.metricProjector
  rw [W.drazin_transport, W.moorePenrose_transport]
  noncomm_ring

/-- With transported metric transport, mismatch transports covariantly. -/
theorem transported_mismatch_covariant
    {P P' : ProjectorPair R}
    (W : SimilarityTransport P P')
    (hTearZero : MPFixedTear P P' W = 0) :
    mismatch_G P' = W.g * mismatch_G P * W.gInv := by
  have h := mismatch_transport_decomposition (W := W)
  rw [hTearZero, sub_zero] at h
  exact h

/-- Transporting the metric exactly kills the fixed-metric Moore--Penrose tear term. -/
theorem mpFixedTear_eq_zero_of_similarityTransport
    {P P' : ProjectorPair R}
    (W : SimilarityTransport P P') :
    MPFixedTear P P' W = 0 := by
  unfold MPFixedTear
  rw [W.moorePenrose_transport]
  exact sub_self _

/-- Direct covariance theorem from the similarity transport owner data. -/
theorem mismatch_covariant_of_similarityTransport
    {P P' : ProjectorPair R}
    (W : SimilarityTransport P P') :
    mismatch_G P' = W.g * mismatch_G P * W.gInv :=
  transported_mismatch_covariant W (mpFixedTear_eq_zero_of_similarityTransport W)

end MetricTransport
