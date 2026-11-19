/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Algebra.Sp4Contact
import InfoGeometry.Core.PeirceWeylUnits
import Mathlib.RingTheory.Nilpotent.Basic

/-!
# Generalized inverses and two Weyl rotations of the contact endpoints

The normalized contact endpoints are a concrete Moore–Penrose pair in the
full real matrix ring. Their supports are distinct commuting projections;
the endpoints themselves do not commute. The existing generic Weyl unit
acts by the identity on the middle plane. Its square is therefore a sign
change only on the endpoint support. A separately chosen rotation of the
middle plane gives the full rotation `-omega` with square `-1`.

These are finite matrix identities. No covering space, spin representation,
analytic holonomy, or interpretation as fermion parity is asserted.
-/

noncomputable section

namespace InfoGeometry.Algebra.Sp4Contact

open Matrix
open InfoGeometry.Singular.MoorePenrose
open InfoGeometry.Core.DiracSuperalgebra
open InfoGeometry.Core.PeirceWeylUnits

theorem zPlus_matrix :
    (zPlus : Mat) = !![0, 0, 0, 1; 0, 0, 0, 0; 0, 0, 0, 0; 0, 0, 0, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [zPlus, generator, matrixOfCoordinates, Pi.single_apply]

theorem zMinus_matrix :
    (zMinus : Mat) = !![0, 0, 0, 0; 0, 0, 0, 0; 0, 0, 0, 0; 1, 0, 0, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [zMinus, generator, matrixOfCoordinates, Pi.single_apply]

theorem zPlus_sq_zero : (zPlus : Mat) * (zPlus : Mat) = 0 := by
  rw [zPlus_matrix]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.mul_apply, Fin.sum_univ_succ]

/-- All four Penrose equations, including self-adjointness of both products. -/
theorem endpoints_moorePenrose :
    IsMoorePenroseInverse (zPlus : Mat) (zMinus : Mat) := by
  rw [IsMoorePenroseInverse, zPlus_matrix, zMinus_matrix]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> ext i j <;>
    fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.mul_apply, Fin.sum_univ_succ, Matrix.star_apply]

theorem reversed_endpoints_moorePenrose :
    IsMoorePenroseInverse (zMinus : Mat) (zPlus : Mat) :=
  ⟨endpoints_moorePenrose.bab_eq_b, endpoints_moorePenrose.aba_eq_a,
    endpoints_moorePenrose.ba_adj_eq, endpoints_moorePenrose.ab_adj_eq⟩

theorem zMinus_sq_zero : (zMinus : Mat) * (zMinus : Mat) = 0 :=
  endpoints_moorePenrose.inverse_sq_eq_zero zPlus_sq_zero

theorem zPlus_not_isUnit : ¬ IsUnit (zPlus : Mat) :=
  IsNilpotent.not_isUnit ⟨2, by simpa only [pow_two] using zPlus_sq_zero⟩

theorem zMinus_not_isUnit : ¬ IsUnit (zMinus : Mat) :=
  IsNilpotent.not_isUnit ⟨2, by simpa only [pow_two] using zMinus_sq_zero⟩

theorem endpoint_exactSupport_matrix :
    exactSupport (zPlus : Mat) (zMinus : Mat) =
      !![1, 0, 0, 0; 0, 0, 0, 0; 0, 0, 0, 0; 0, 0, 0, 0] := by
  rw [exactSupport, zPlus_matrix, zMinus_matrix]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.mul_apply, Fin.sum_univ_succ]

theorem endpoint_coexactSupport_matrix :
    coexactSupport (zPlus : Mat) (zMinus : Mat) =
      !![0, 0, 0, 0; 0, 0, 0, 0; 0, 0, 0, 0; 0, 0, 0, 1] := by
  rw [coexactSupport, zPlus_matrix, zMinus_matrix]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.mul_apply, Fin.sum_univ_succ]

theorem endpoint_activeSupport_matrix :
    activeSupport (zPlus : Mat) (zMinus : Mat) =
      !![1, 0, 0, 0; 0, 0, 0, 0; 0, 0, 0, 0; 0, 0, 0, 1] := by
  rw [activeSupport, endpoint_exactSupport_matrix, endpoint_coexactSupport_matrix]
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num

theorem endpoint_harmonicSupport_matrix :
    harmonicSupport (zPlus : Mat) (zMinus : Mat) =
      !![0, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 0] := by
  rw [harmonicSupport, endpoint_exactSupport_matrix, endpoint_coexactSupport_matrix]
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num

theorem endpoint_supports_orthogonal :
    exactSupport (zPlus : Mat) (zMinus : Mat) *
        coexactSupport (zPlus : Mat) (zMinus : Mat) = 0 ∧
      coexactSupport (zPlus : Mat) (zMinus : Mat) *
        exactSupport (zPlus : Mat) (zMinus : Mat) = 0 :=
  ⟨endpoints_moorePenrose.range_mul_domain_eq_zero zPlus_sq_zero,
    IsMoorePenroseInverse.domain_mul_range_eq_zero zPlus_sq_zero⟩

theorem endpoint_supports_commute :
    Commute (exactSupport (zPlus : Mat) (zMinus : Mat))
      (coexactSupport (zPlus : Mat) (zMinus : Mat)) := by
  change _ * _ = _ * _
  rw [endpoint_supports_orthogonal.1, endpoint_supports_orthogonal.2]

theorem endpoint_supports_ne :
    exactSupport (zPlus : Mat) (zMinus : Mat) ≠
      coexactSupport (zPlus : Mat) (zMinus : Mat) := by
  intro h
  have h00 := congrArg (fun M : Mat => M 0 0) h
  norm_num [endpoint_exactSupport_matrix, endpoint_coexactSupport_matrix] at h00

/-- Existing generic unit, with the orientation `F - E` on the endpoint plane. -/
def endpointWeyl : Matˣ :=
  weylUnit reversed_endpoints_moorePenrose zMinus_sq_zero

theorem endpointWeyl_matrix :
    (endpointWeyl : Mat) =
      !![0, 0, 0, -1; 0, 1, 0, 0; 0, 0, 1, 0; 1, 0, 0, 0] := by
  change weylElement (zMinus : Mat) (zPlus : Mat) = _
  simp only [weylElement, harmonicSupport, exactSupport, coexactSupport,
    majoranaMinus, zPlus_matrix, zMinus_matrix]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.mul_apply, Fin.sum_univ_succ]

/-- The completed endpoint exchange preserves the fixed symplectic form. -/
theorem endpointWeyl_symplectic :
    (endpointWeyl : Mat).transpose * omega * (endpointWeyl : Mat) = omega := by
  rw [endpointWeyl_matrix]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [omega, Matrix.mul_apply, Fin.sum_univ_succ]

/-- The square changes sign only on the two-dimensional endpoint support. -/
theorem endpointWeyl_sq :
    (endpointWeyl : Mat) * (endpointWeyl : Mat) =
      1 - (2 : ℝ) • activeSupport (zPlus : Mat) (zMinus : Mat) := by
  change weylElement (zMinus : Mat) (zPlus : Mat) *
    weylElement (zMinus : Mat) (zPlus : Mat) = _
  rw [weyl_square reversed_endpoints_moorePenrose zMinus_sq_zero]
  simp only [harmonicSupport, activeSupport, exactSupport, coexactSupport]
  module

theorem endpointWeyl_fourth : endpointWeyl ^ 4 = 1 := by
  apply Units.ext
  exact weyl_fourth reversed_endpoints_moorePenrose zMinus_sq_zero

theorem endpointWeyl_sq_ne_one :
    (endpointWeyl : Mat) * (endpointWeyl : Mat) ≠ 1 := by
  intro h
  have h00 := congrArg (fun M : Mat => M 0 0) h
  norm_num [endpointWeyl_sq, endpoint_activeSupport_matrix] at h00

theorem endpointWeyl_sq_ne_neg_one :
    (endpointWeyl : Mat) * (endpointWeyl : Mat) ≠ -1 := by
  intro h
  have h11 := congrArg (fun M : Mat => M 1 1) h
  norm_num [endpointWeyl_sq, endpoint_activeSupport_matrix] at h11

theorem endpointWeyl_conjugates_zPlus :
    (endpointWeyl : Mat) * (zPlus : Mat) * ((endpointWeyl⁻¹ : Matˣ) : Mat) =
      -(zMinus : Mat) :=
  (weyl_conjugation reversed_endpoints_moorePenrose zMinus_sq_zero).2.2.2

theorem endpointWeyl_fold_defect :
    let T : Mat := (1 / 2 : ℝ) • (1 + (endpointWeyl : Mat))
    T * T - T = (-1 / 2 : ℝ) • activeSupport (zPlus : Mat) (zMinus : Mat) := by
  dsimp
  rw [endpointWeyl_matrix, endpoint_activeSupport_matrix]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply]

/-- A separate choice rotates both the endpoint plane and the middle plane. -/
def fullRotation : Matˣ where
  val := -omega
  inv := omega
  val_inv := by rw [neg_mul, omega_sq, neg_neg]
  inv_val := by rw [mul_neg, omega_sq, neg_neg]

theorem fullRotation_sq : (fullRotation : Mat) * (fullRotation : Mat) = -1 := by
  change (-omega) * (-omega) = -1
  rw [neg_mul_neg, omega_sq]

theorem fullRotation_fourth : fullRotation ^ 4 = 1 := by
  apply Units.ext
  change (fullRotation : Mat) ^ 4 = 1
  calc
    (fullRotation : Mat) ^ 4 =
        ((fullRotation : Mat) * (fullRotation : Mat)) *
          ((fullRotation : Mat) * (fullRotation : Mat)) := by noncomm_ring
    _ = 1 := by rw [fullRotation_sq]; norm_num

theorem fullRotation_symplectic :
    (fullRotation : Mat).transpose * omega * (fullRotation : Mat) = omega := by
  change (-omega).transpose * omega * (-omega) = omega
  rw [Matrix.transpose_neg, omega_transpose, neg_neg, omega_sq]
  simp

theorem fullRotation_conjugates_zPlus :
    (fullRotation : Mat) * (zPlus : Mat) * ((fullRotation⁻¹ : Matˣ) : Mat) =
      -(zMinus : Mat) := by
  change (-omega) * (zPlus : Mat) * omega = -(zMinus : Mat)
  rw [zPlus_matrix, zMinus_matrix]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [omega, Matrix.mul_apply, Fin.sum_univ_succ]

theorem fullRotation_fold_defect :
    let T : Mat := (1 / 2 : ℝ) • (1 + (fullRotation : Mat))
    T * T - T = (-1 / 2 : ℝ) • (1 : Mat) := by
  dsimp only
  simp only [smul_mul_assoc, mul_smul_comm, add_mul, mul_add,
    one_mul, mul_one, fullRotation_sq]
  module

end InfoGeometry.Algebra.Sp4Contact
