import InfoGeometry.Canonical.OperatorProjectorMismatch
import InfoGeometry.Canonical.MetricTransport
import Mathlib.Tactic

/-!
# Conformal projector agreement

Phase C fixed-metric boundary:

`MetricTransport` owns the positive transport API.  This file owns only the
finite matrix counterexample showing that fixed Euclidean Moore--Penrose
projectors are not generically similarity-equivariant.
-/

namespace InfoGeometry.Canonical.ConformalProjectorAgreement

open InfoGeometry.Canonical.OperatorProjectorMismatch
open InfoGeometry.Canonical.MetricTransport

variable {R : Type*} [Ring R]

-- Conformal property layer: explicit one-way transport bridges for diagnostic tests.
-- - DrazinSimilarityTransportData: similarity transport of the Drazin projector.
-- - MoorePenroseMetricTransportData: metric transport of the Moore--Penrose projector.
-- - ConformalMismatchTransportData: mismatch transport decomposition.


/-- Drazin projector similarity transport property. -/
structure DrazinSimilarityTransportData (P P' : ProjectorPair R) where
  g : R
  gInv : R
  leftInv : gInv * g = 1
  rightInv : g * gInv = 1
  drazinProjector_transport : P'.PD = g * P.PD * gInv

/-- Moore--Penrose projector metric transport property. -/
structure MoorePenroseMetricTransportData (P P' : ProjectorPair R) where
  g : R
  gInv : R
  leftInv : gInv * g = 1
  rightInv : g * gInv = 1
  moorePenroseProjector_transport : P'.PMP = g * P.PMP * gInv

/-- Conformal mismatch transport property. -/
structure ConformalMismatchTransportData (P P' : ProjectorPair R) where
  transport : SimilarityTransport P P'
  mismatch_fixedMetric_decomposition :
    mismatch_G P' = transport.g * mismatch_G P * transport.gInv - MPFixedTear P P' transport

/--
Similarity transport of the Drazin projector is the core one-way naturality route.
This is intentionally explicit to avoid hidden assumptions.
-/
theorem drazinProjector_equivariant
    {P P' : ProjectorPair R}
    (W : DrazinSimilarityTransportData P P') :
    P'.PD = W.g * P.PD * W.gInv :=
  W.drazinProjector_transport

/--
Similarity transport of the Moore--Penrose projector is not arbitrary in this lane.
`metric-natural` naming marks the intended restricted surface.
-/
theorem moorePenroseProjector_equivariant_of_metricData
    {P P' : ProjectorPair R}
    (W : MoorePenroseMetricTransportData P P') :
    P'.PMP = W.g * P.PMP * W.gInv :=
  W.moorePenroseProjector_transport

/-- Alias naming expected by historical phase tests. -/
def MPFixedMetricTear (P P' : ProjectorPair R)
    (W : SimilarityTransport P P') :
    R :=
  MPFixedTear P P' W

/-- Alias naming expected by historical phase tests. -/
theorem mismatch_fixedMetric_decomposition
    {P P' : ProjectorPair R}
    (W : SimilarityTransport P P') :
    mismatch_G P' = W.g * mismatch_G P * W.gInv - MPFixedMetricTear P P' W := by
  simpa [MPFixedMetricTear] using mismatch_transport_decomposition (W := W)

/-
The concrete `2×2` property remains the negative boundary counterexample for fixed
Euclidean similarity-naturality/metric-naturality mismatch.

Tags in this section include `similarity-natural` and `metric-natural`.
-/
/-- ## 2×2 fixed Euclidean shear counterexample -/

abbrev Mat2 := Matrix (Fin 2) (Fin 2) ℚ

def shearA : Mat2 := !![1, 0; 0, 0]
def shearG : Mat2 := !![1, 1; 0, 1]
def shearGInv : Mat2 := !![1, -1; 0, 1]
def shearAprime : Mat2 := !![1, -1; 0, 0]

def shearDrazinZeroAprime : Mat2 := !![0, 1; 0, 1]
def shearEuclideanMPZeroAprime : Mat2 :=
  !![(1 / 2 : ℚ), (1 / 2 : ℚ); (1 / 2 : ℚ), (1 / 2 : ℚ)]
def shearEuclideanMPZeroA : Mat2 := !![0, 0; 0, 1]

theorem shearA_idempotent :
    shearA * shearA = shearA := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [shearA, Matrix.mul_apply, Fin.sum_univ_two]

theorem shearAprime_idempotent :
    shearAprime * shearAprime = shearAprime := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [shearAprime, Matrix.mul_apply, Fin.sum_univ_two]

theorem shearEuclideanMPZeroA_idempotent :
    shearEuclideanMPZeroA * shearEuclideanMPZeroA = shearEuclideanMPZeroA := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [shearEuclideanMPZeroA, Matrix.mul_apply, Fin.sum_univ_two]

theorem shearEuclideanMPZeroAprime_idempotent :
    shearEuclideanMPZeroAprime * shearEuclideanMPZeroAprime =
      shearEuclideanMPZeroAprime := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [shearEuclideanMPZeroAprime, Matrix.mul_apply, Fin.sum_univ_two]

theorem shearCounterexample_Aprime_eq :
    shearG * shearA * shearGInv = shearAprime := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [shearG, shearA, shearGInv, shearAprime, Matrix.mul_apply, Fin.sum_univ_two]

theorem shearCounterexample_G_mul_GInv :
    shearG * shearGInv = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [shearG, shearGInv, Matrix.mul_apply, Fin.sum_univ_two]

theorem shearCounterexample_GInv_mul_G :
    shearGInv * shearG = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [shearG, shearGInv, Matrix.mul_apply, Fin.sum_univ_two]

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

/--
Negative boundary: a concrete `2 × 2` shear gives similarity transport of the
Drazin projector while the fixed Euclidean Moore--Penrose projector fails to
transport by the same similarity.
-/
theorem moorePenrose_not_generic_similarity_equivariant_under_fixed_metric :
    ∃ (S : Type 0) (_ : Ring S) (P P' : ProjectorPair S) (g gInv : S),
      g * gInv = 1 ∧ gInv * g = 1 ∧
      P'.PD = g * P.PD * gInv ∧
      P'.PMP ≠ g * P.PMP * gInv := by
  let P : ProjectorPair Mat2 :=
    { PD := shearA
      PMP := shearEuclideanMPZeroA
      PD_idempotent := shearA_idempotent
      PMP_idempotent := shearEuclideanMPZeroA_idempotent }
  let P' : ProjectorPair Mat2 :=
    { PD := shearAprime
      PMP := shearEuclideanMPZeroAprime
      PD_idempotent := shearAprime_idempotent
      PMP_idempotent := shearEuclideanMPZeroAprime_idempotent }
  refine ⟨Mat2, inferInstance, P, P', shearG, shearGInv, ?_, ?_, ?_, ?_⟩
  · exact shearCounterexample_G_mul_GInv
  · exact shearCounterexample_GInv_mul_G
  · simpa [P, P'] using shearCounterexample_Aprime_eq.symm
  · simpa [P, P'] using shearCounterexample_fixedMetric_MP_transport_fails

end InfoGeometry.Canonical.ConformalProjectorAgreement
