/- SPDX-License-Identifier: Apache-2.0 -/

import Mathlib

/-!
# The elementary n-potent polynomial identity

This owner records the purely associative algebra used by the n-potent part
of the accompanying architectural note.  It makes no spectral or operator
theoretic claim and is independent of the split-octonion carrier.
-/

namespace InfoGeometry.Algebra.Zorn.G2NPotentPolynomialBridge

theorem pow_eq_self_iff_mul_pow_sub_one_eq_zero
    {R : Type*} [Ring R] (n : ℕ) (hn : 1 ≤ n) (x : R) :
    x ^ n = x ↔ x * (x ^ (n - 1) - 1) = 0 := by
  have hpow : x * x ^ (n - 1) = x ^ n := by
    rw [← pow_succ']
    congr
    omega
  rw [mul_sub, mul_one, hpow]
  constructor <;> intro h
  · rw [h]
    exact sub_self x
  · exact sub_eq_zero.mp h

theorem pow_eq_self_iff_eq_zero_or_pow_pred_eq_one
    {R : Type*} [Field R] (n : ℕ) (hn : 2 ≤ n) (x : R) :
    x ^ n = x ↔ x = 0 ∨ x ^ (n - 1) = 1 := by
  constructor
  · intro h
    have hmul : x * (x ^ (n - 1) - 1) = 0 :=
      (pow_eq_self_iff_mul_pow_sub_one_eq_zero n (by omega) x).mp h
    rcases mul_eq_zero.mp hmul with hx | hrest
    · exact Or.inl hx
    · exact Or.inr (sub_eq_zero.mp hrest)
  · rintro (rfl | h)
    · have hn0 : n ≠ 0 := by omega
      simp [hn0]
    · apply (pow_eq_self_iff_mul_pow_sub_one_eq_zero n (by omega) x).mpr
      rw [h, sub_self]
      exact mul_zero x

theorem one_add_mul_neg_geom_sum_eq_one_of_pow_eq_zero
    {R : Type*} [Ring R] {x : R} {n : ℕ}
    (hx : x ^ n = 0) :
    (1 + x) * (∑ i ∈ Finset.range n, (-x) ^ i) = 1 := by
  have h := mul_geom_sum (-x) n
  have hneg : (-x) ^ n = 0 := by
    rw [neg_pow, hx]
    simp
  have h' : (-x - 1) * (∑ i ∈ Finset.range n, (-x) ^ i) = -1 := by
    rw [hneg] at h
    simpa only [zero_sub] using h
  calc
    (1 + x) * (∑ i ∈ Finset.range n, (-x) ^ i) =
        -((-x - 1) * (∑ i ∈ Finset.range n, (-x) ^ i)) := by
      rw [show 1 + x = -(-x - 1) by noncomm_ring, neg_mul]
    _ = -(-1) := by rw [h']
    _ = 1 := by simp

theorem neg_geom_sum_mul_one_add_eq_one_of_pow_eq_zero
    {R : Type*} [Ring R] {x : R} {n : ℕ}
    (hx : x ^ n = 0) :
    (∑ i ∈ Finset.range n, (-x) ^ i) * (1 + x) = 1 := by
  have h := geom_sum_mul (-x) n
  have hneg : (-x) ^ n = 0 := by
    rw [neg_pow, hx]
    simp
  have h' : (∑ i ∈ Finset.range n, (-x) ^ i) * (-x - 1) = -1 := by
    rw [hneg] at h
    simpa only [zero_sub] using h
  calc
    (∑ i ∈ Finset.range n, (-x) ^ i) * (1 + x) =
        -((∑ i ∈ Finset.range n, (-x) ^ i) * (-x - 1)) := by
      rw [show 1 + x = -(-x - 1) by noncomm_ring, mul_neg]
    _ = -(-1) := by rw [h']
    _ = 1 := by simp

end InfoGeometry.Algebra.Zorn.G2NPotentPolynomialBridge
