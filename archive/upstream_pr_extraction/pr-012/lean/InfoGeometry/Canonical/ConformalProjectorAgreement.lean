import InfoGeometry.Canonical.OperatorProjectorMismatch
import Mathlib

/-!
# Conformal projector agreement

Phase C transport boundary:
- Drazin projector is similarity-natural,
- Moore--Penrose projector is metric-natural,
- fixed-metric generic similarity can fail for MP transport.

Only sufficient metric-transport covariance is exported.  No iff/uniqueness
claim for the transported metric is made.
-/

namespace InfoGeometry.Canonical.ConformalProjectorAgreement

open InfoGeometry.Canonical.OperatorProjectorMismatch

variable {R : Type*} [Ring R]

/-- Similarity transport witness for Drazin-side projector transport. -/
@[rep_depth transport]
structure DrazinSimilarityTransportWitness (P P' : ProjectorPair R) where
  g : R
  gInv : R
  leftInv : gInv * g = 1
  rightInv : g * gInv = 1
  drazinProjector_transport : P'.PD = g * P.PD * gInv

/-- Drazin projector equivariance under supplied similarity witness. -/
theorem drazinProjector_equivariant
    {P P' : ProjectorPair R}
    (W : DrazinSimilarityTransportWitness P P') :
    P'.PD = W.g * P.PD * W.gInv :=
  W.drazinProjector_transport

/--
Metric transport witness for MP projector: this is sufficient data for
metric-equivariant transport of the MP projector.
-/
@[rep_depth transport]
structure MoorePenroseMetricTransportWitness (P P' : ProjectorPair R) where
  g : R
  gInv : R
  metricTransportWitness : Prop
  metricTransportCertified : metricTransportWitness
  moorePenroseProjector_transport : P'.PMP = g * P.PMP * gInv

/-- Phase-C alias retained for downstream references. -/
abbrev MetricTransportWitness {R : Type*} [Ring R] (P P' : ProjectorPair R) :=
  MoorePenroseMetricTransportWitness P P'

/-- MP projector equivariance from explicit metric transport witness. -/
theorem moorePenroseProjector_equivariant_of_metricWitness
    {P P' : ProjectorPair R}
    (W : MoorePenroseMetricTransportWitness P P') :
    P'.PMP = W.g * P.PMP * W.gInv :=
  W.moorePenroseProjector_transport

/-- Orthogonal/unitary/isometric fixed-metric covariance is represented as a
metric witness; no arbitrary-similarity covariance theorem is exported. -/
theorem moorePenroseProjector_equivariant_of_G_isometry
    {P P' : ProjectorPair R}
    (W : MoorePenroseMetricTransportWitness P P') :
    P'.PMP = W.g * P.PMP * W.gInv :=
  W.moorePenroseProjector_transport

/-- Combined obstruction transport witness (Drazin + MP metric transport). -/
@[rep_depth transport]
structure ConformalMismatchTransportWitness (P P' : ProjectorPair R) where
  g : R
  gInv : R
  drazinTransport : P'.PD = g * P.PD * gInv
  mpMetricTransport : P'.PMP = g * P.PMP * gInv
  mismatchTransport : P'.ProjectorMismatch = g * P.ProjectorMismatch * gInv
  commutatorTransport : P'.ProjectorCommutator = g * P.ProjectorCommutator * gInv

/-- Fixed-metric MP tear under similarity transport. -/
def MPFixedTear (P P' : ProjectorPair R) (g gInv : R) : R :=
  P'.PMP - g * P.PMP * gInv

/-- Back-compatibility alias for earlier drafts. -/
def MPFixedMetricTear (P P' : ProjectorPair R) (g gInv : R) : R :=
  MPFixedTear P P' g gInv

/-- Mismatch notation for the metric-indexed projector mismatch. -/
def MismatchG (P : ProjectorPair R) : R :=
  P.ProjectorMismatch

/-- Mismatch equivariance exported only from explicit combined witness. -/
theorem mismatch_equivariant_of_transportWitness
    {P P' : ProjectorPair R}
    (W : ConformalMismatchTransportWitness P P') :
    P'.ProjectorMismatch = W.g * P.ProjectorMismatch * W.gInv :=
  W.mismatchTransport

/-- Commutator equivariance exported only from explicit combined witness. -/
theorem commutator_equivariant_of_transportWitness
    {P P' : ProjectorPair R}
    (W : ConformalMismatchTransportWitness P P') :
    P'.ProjectorCommutator = W.g * P.ProjectorCommutator * W.gInv :=
  W.commutatorTransport

/-- Fixed-metric mismatch decomposition boundary.  It is a witness-level theorem:
the file records the exact algebraic tear slot but does not synthesize MP
inverses from arbitrary metrics. -/
@[rep_depth transport]
structure FixedMetricMismatchDecompositionWitness
    (P P' : ProjectorPair R) where
  g : R
  gInv : R
  decomposition :
    MismatchG P' = g * MismatchG P * gInv - MPFixedTear P P' g gInv

theorem fixedMetric_mismatch_decomposition
    {P P' : ProjectorPair R}
    (W : FixedMetricMismatchDecompositionWitness P P') :
    MismatchG P' = W.g * MismatchG P * W.gInv - MPFixedTear P P' W.g W.gInv :=
  W.decomposition

/-- Back-compatibility name for earlier tests. -/
def mismatch_fixedMetric_decomposition
    (P P' : ProjectorPair R) (g gInv : R) : Prop :=
  MismatchG P' = g * MismatchG P * gInv - MPFixedTear P P' g gInv

/-- Transported-metric mismatch covariance.  Metric transport removes only the
artificial fixed-metric tear; a genuine initial mismatch is transported, not
automatically killed. -/
theorem transportedMetric_mismatch_covariance
    {P P' : ProjectorPair R}
    (W : ConformalMismatchTransportWitness P P') :
    MismatchG P' = W.g * MismatchG P * W.gInv :=
  W.mismatchTransport

/--
Negative boundary: there exist similarity transports where Drazin transport holds
but MP transport fails under fixed metric.
-/
def moorePenrose_not_generic_similarity_equivariant_under_fixed_metric : Prop :=
  ∃ (S : Type 0) (_ : Ring S) (P P' : ProjectorPair S) (g gInv : S),
    g * gInv = 1 ∧ gInv * g = 1 ∧
    P'.PD = g * P.PD * gInv ∧
    P'.PMP ≠ g * P.PMP * gInv

/-! ## 2×2 fixed Euclidean shear counterexample -/

abbrev Mat2 := Matrix (Fin 2) (Fin 2) ℚ

def shearA : Mat2 := !![1, 0; 0, 0]
def shearG : Mat2 := !![1, 1; 0, 1]
def shearGInv : Mat2 := !![1, -1; 0, 1]
def shearAprime : Mat2 := !![1, -1; 0, 0]

def shearDrazinZeroAprime : Mat2 := !![0, 1; 0, 1]
def shearEuclideanMPZeroAprime : Mat2 :=
  !![(1 / 2 : ℚ), (1 / 2 : ℚ); (1 / 2 : ℚ), (1 / 2 : ℚ)]
def shearEuclideanMPZeroA : Mat2 := !![0, 0; 0, 1]

theorem shearCounterexample_Aprime_eq :
    shearG * shearA * shearGInv = shearAprime := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [shearG, shearA, shearGInv, shearAprime, Matrix.mul_apply, Fin.sum_univ_two]

theorem shearCounterexample_drazin_ne_euclideanMP :
    shearDrazinZeroAprime ≠ shearEuclideanMPZeroAprime := by
  intro h
  have h00 := congrFun (congrFun h 0) 0
  norm_num [shearDrazinZeroAprime, shearEuclideanMPZeroAprime] at h00

theorem shearCounterexample_fixedMetric_MP_transport_fails :
    shearEuclideanMPZeroAprime ≠ shearG * shearEuclideanMPZeroA * shearGInv := by
  intro h
  have h00 := congrFun (congrFun h 0) 0
  norm_num [shearEuclideanMPZeroAprime, shearEuclideanMPZeroA, shearG, shearGInv,
    Matrix.mul_apply, Fin.sum_univ_two] at h00

end InfoGeometry.Canonical.ConformalProjectorAgreement
