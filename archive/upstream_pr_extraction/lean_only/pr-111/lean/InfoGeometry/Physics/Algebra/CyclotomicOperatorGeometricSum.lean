/- SPDX-License-Identifier: Apache-2.0 -/

import Mathlib

/-!
# The algebraic geometric-sum identity behind finite cyclotomic projectors

Only the telescoping identity is recorded here.  Spectral decomposition and
orthogonality require additional hypotheses and are intentionally separate.
-/

namespace InfoGeometry.Physics.Algebra.CyclotomicOperatorGeometricSum

theorem one_sub_mul_geom_sum (R : Type*) [Ring R] (U : R) (n : ℕ) :
    (1 - U) * (∑ i ∈ Finset.range n, U ^ i) = 1 - U ^ n := by
  have h := mul_geom_sum U n
  calc
    (1 - U) * (∑ i ∈ Finset.range n, U ^ i) =
        -((U - 1) * (∑ i ∈ Finset.range n, U ^ i)) := by
      noncomm_ring
    _ = -(U ^ n - 1) := by rw [h]
    _ = 1 - U ^ n := by noncomm_ring

theorem one_sub_mul_geom_sum_eq_zero_of_pow_eq_one
    (R : Type*) [Ring R] (U : R) (n : ℕ) (hU : U ^ n = 1) :
    (1 - U) * (∑ i ∈ Finset.range n, U ^ i) = 0 := by
  rw [one_sub_mul_geom_sum, hU, sub_self]

theorem geom_sum_mul_one_sub (R : Type*) [Ring R] (U : R) (n : ℕ) :
    (∑ i ∈ Finset.range n, U ^ i) * (1 - U) = 1 - U ^ n := by
  have h := geom_sum_mul U n
  calc
    (∑ i ∈ Finset.range n, U ^ i) * (1 - U) =
        -((∑ i ∈ Finset.range n, U ^ i) * (U - 1)) := by
      noncomm_ring
    _ = -(U ^ n - 1) := by rw [h]
    _ = 1 - U ^ n := by simp [sub_eq_add_neg, add_comm]

theorem geom_sum_mul_one_sub_eq_zero_of_pow_eq_one
    (R : Type*) [Ring R] (U : R) (n : ℕ) (hU : U ^ n = 1) :
    (∑ i ∈ Finset.range n, U ^ i) * (1 - U) = 0 := by
  rw [geom_sum_mul_one_sub, hU, sub_self]

theorem involution_average_idempotent
    (R : Type*) [Field R] [CharZero R] (U : R) (hU : U ^ 2 = 1) :
    ((1 + U) / 2) ^ 2 = (1 + U) / 2 := by
  field_simp
  calc
    (1 + U) ^ 2 = (1 + U) * (1 + U) := by rw [pow_two]
    _ = 1 + U + U + U * U := by noncomm_ring
    _ = (1 + U) * 2 := by rw [← hU]; noncomm_ring

theorem involution_complement_idempotent
    (R : Type*) [Field R] [CharZero R] (U : R) (hU : U ^ 2 = 1) :
    ((1 - U) / 2) ^ 2 = (1 - U) / 2 := by
  field_simp
  calc
    (1 - U) ^ 2 = (1 - U) * (1 - U) := by rw [pow_two]
    _ = 1 - U - U + U * U := by noncomm_ring
    _ = (1 - U) * 2 := by rw [← hU]; noncomm_ring

theorem involution_average_orthogonal
    (R : Type*) [Field R] [CharZero R] (U : R) (hU : U ^ 2 = 1) :
    ((1 + U) / 2) * ((1 - U) / 2) = 0 ∧
      ((1 - U) / 2) * ((1 + U) / 2) = 0 := by
  constructor
  · field_simp
    calc
      (1 + U) * (1 - U) = 1 - U * U := by noncomm_ring
      _ = 0 := by rw [← pow_two, hU, sub_self]
      _ = 2 ^ 2 * 0 := by simp
  · field_simp
    calc
      (1 - U) * (1 + U) = 1 - U * U := by noncomm_ring
      _ = 0 := by rw [← pow_two, hU, sub_self]
      _ = 2 ^ 2 * 0 := by simp

theorem involution_average_resolves_identity
    (R : Type*) [Field R] [CharZero R] (U : R) :
    (1 + U) / 2 + (1 - U) / 2 = 1 := by
  ring

theorem involution_average_reconstructs
    (R : Type*) [Field R] [CharZero R] (U : R) :
    (1 + U) / 2 - (1 - U) / 2 = U := by
  ring

theorem order_three_average_idempotent
    (R : Type*) [Field R] [CharZero R] (U : R) (hU : U ^ 3 = 1) :
    ((1 + U + U ^ 2) / 3) ^ 2 = (1 + U + U ^ 2) / 3 := by
  have h4 : U ^ 4 = U := by
    calc
      U ^ 4 = U ^ 3 * U := by
        rw [show 4 = 3 + 1 by norm_num, pow_add, pow_one]
      _ = U := by rw [hU, one_mul]
  field_simp
  rw [pow_two]
  ring_nf
  rw [h4, hU]
  ring

theorem order_four_average_idempotent
    (R : Type*) [Field R] [CharZero R] (U : R) (hU : U ^ 4 = 1) :
    ((1 + U + U ^ 2 + U ^ 3) / 4) ^ 2 =
      (1 + U + U ^ 2 + U ^ 3) / 4 := by
  have h5 : U ^ 5 = U := by
    calc
      U ^ 5 = U ^ 4 * U := by
        rw [show 5 = 4 + 1 by norm_num, pow_add, pow_one]
      _ = U := by rw [hU, one_mul]
  have h6 : U ^ 6 = U ^ 2 := by
    calc
      U ^ 6 = U ^ 4 * U ^ 2 := by
        rw [show 6 = 4 + 2 by norm_num, pow_add]
      _ = U ^ 2 := by rw [hU, one_mul]
  field_simp
  rw [pow_two]
  ring_nf
  rw [hU, h5, h6]
  ring

end InfoGeometry.Physics.Algebra.CyclotomicOperatorGeometricSum
