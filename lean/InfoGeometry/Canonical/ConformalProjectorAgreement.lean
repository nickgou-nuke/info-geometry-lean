import InfoGeometry.Canonical.OperatorProjectorMismatch
import InfoGeometry.Canonical.MetricTransport
import Mathlib

/-!
# Conformal projector agreement

Phase C fixed-metric boundary:

`MetricTransport` owns the positive transport API.  This file owns only the
finite matrix counterexample showing that fixed Euclidean Moore--Penrose
projectors are not generically similarity-equivariant.
-/

namespace ConformalProjectorAgreement

open InfoGeometry.Canonical.OperatorProjectorMismatch

variable {R : Type*} [Ring R]

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

end ConformalProjectorAgreement
