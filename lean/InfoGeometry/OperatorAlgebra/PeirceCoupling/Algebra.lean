/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Core.PeirceGrading

/-!
# Opposite Peirce products

Two independent inputs supply opposite corners of an arbitrary idempotent.
The existing reflection converts their Jordan product into their native Lie
bracket. All identities hold in an associative ring, with no commutativity,
adjoint, positivity, or cancellation-of-two hypothesis.
-/

namespace InfoGeometry.OperatorAlgebra.PeirceCoupling

open InfoGeometry.Core.PeirceDecomposition InfoGeometry.Core.PeirceGrading

variable {A : Type*} [Ring A] {p : A} (hp : IsIdempotentElem p) (a b : A)

local notation "U" => component10 p a
local notation "V" => component01 p b
local notation "J" => U * V + V * U
local notation "K" => ⁅U, V⁆
local notation "S" => reflection p

include hp

private theorem left_upper : p * U = U :=
  peirceCorner_absorb_left hp.eq

private theorem right_upper : U * p = 0 := by
  change (p * a * complementIdempotent p) * p = 0
  rw [mul_assoc, complement_mul_idempotent p hp.eq, mul_zero]

private theorem left_lower : p * V = 0 := by
  change p * (complementIdempotent p * b * p) = 0
  calc
    _ = (p * complementIdempotent p) * (b * p) := by simp only [mul_assoc]
    _ = 0 := by rw [idempotent_mul_complement p hp.eq, zero_mul]

private theorem right_lower : V * p = V :=
  peirceCorner_absorb_right hp.eq

/-- Independently chosen opposite corners give an algebraic tangent direction. -/
theorem opposite_sum_tangent : p * (U + V) + (U + V) * p = U + V := by
  rw [mul_add, add_mul, left_upper hp, left_lower hp, right_upper hp, right_lower hp]
  simp

/-- The sum of the two corners squares to their Jordan product. -/
theorem opposite_sum_sq : (U + V) ^ 2 = J := by
  have hu : U * U = 0 := peirceCorner_sq_eq_zero (complement_mul_idempotent p hp.eq)
  have hv : V * V = 0 := peirceCorner_sq_eq_zero (idempotent_mul_complement p hp.eq)
  rw [pow_two, add_mul, mul_add, mul_add, hu, hv]
  simp

/-- The positive-sector compression of the Lie product. -/
theorem upper_lie_compression : p * K * p = U * V := by
  change p * (U * V - V * U) * p = U * V
  simp only [mul_sub, ← mul_assoc p U, ← mul_assoc p V,
    left_upper hp, left_lower hp, zero_mul, sub_zero]
  rw [mul_assoc, right_lower hp]

/-- The negative-sector compression has the opposite sign. -/
theorem lower_lie_compression : (1 - p) * K * (1 - p) = -(V * U) := by
  have hqu : (1 - p) * U = 0 := by rw [sub_mul, one_mul, left_upper hp]; abel
  have hqv : (1 - p) * V = V := by rw [sub_mul, one_mul, left_lower hp, sub_zero]
  have huq : U * (1 - p) = U := by rw [mul_sub, mul_one, right_upper hp, sub_zero]
  change (1 - p) * (U * V - V * U) * (1 - p) = -(V * U)
  rw [mul_sub (1 - p) (U * V) (V * U), ← mul_assoc (1 - p) U, ← mul_assoc (1 - p) V,
    hqu, hqv, zero_mul, zero_sub, neg_mul, mul_assoc, huq]

theorem upper_jordan_compression : p * J * p = U * V := by
  simp only [mul_add, ← mul_assoc p U, ← mul_assoc p V,
    left_upper hp, left_lower hp, zero_mul, add_zero]
  rw [mul_assoc, right_lower hp]

theorem lower_jordan_compression : (1 - p) * J * (1 - p) = V * U := by
  have hqu : (1 - p) * U = 0 := by rw [sub_mul, one_mul, left_upper hp]; abel
  have hqv : (1 - p) * V = V := by rw [sub_mul, one_mul, left_lower hp, sub_zero]
  have huq : U * (1 - p) = U := by rw [mul_sub, mul_one, right_upper hp, sub_zero]
  rw [mul_add, ← mul_assoc (1 - p) U, ← mul_assoc (1 - p) V,
    hqu, hqv, zero_mul, zero_add, mul_assoc, huq]

/-- The grading turns the two-input Jordan product into the Lie bracket. -/
theorem reflection_mul_jordan : S * J = K := by
  change (2 * p - 1) * (U * V + V * U) = U * V - V * U
  have hpuv : p * (U * V) = U * V := by rw [← mul_assoc, left_upper hp]
  have hpvu : p * (V * U) = 0 := by rw [← mul_assoc, left_lower hp, zero_mul]
  noncomm_ring [hpuv, hpvu]

/-- The converse conversion uses the existing involution law, not a circular proof. -/
theorem reflection_mul_lie : S * K = J := by
  rw [← reflection_mul_jordan hp a b, ← mul_assoc, reflection_sq hp, one_mul]

theorem jordan_eq_zero_iff_lie_eq_zero : J = 0 ↔ K = 0 := by
  constructor
  · intro h
    rw [← reflection_mul_jordan hp a b, h, mul_zero]
  · intro h
    rw [← reflection_mul_lie hp a b, h, mul_zero]

/-- Opposite supports prevent cancellation between the two Jordan summands. -/
theorem jordan_eq_zero_iff_products_eq_zero : J = 0 ↔ U * V = 0 ∧ V * U = 0 := by
  constructor
  · intro h
    constructor
    · rw [← upper_jordan_compression hp a b, h, mul_zero, zero_mul]
    · rw [← lower_jordan_compression hp a b, h, mul_zero, zero_mul]
  · rintro ⟨h₁, h₂⟩
    rw [h₁, h₂, add_zero]

theorem jordan_mem_even : J ∈ LinearMap.range (even p) := by
  rw [mem_even_iff hp]
  simp only [mul_add, add_mul, ← mul_assoc p U, ← mul_assoc p V,
    left_upper hp, left_lower hp, zero_mul, add_zero]
  rw [mul_assoc U V p, mul_assoc V U p, right_lower hp, right_upper hp, mul_zero, add_zero]

theorem lie_mem_even : K ∈ LinearMap.range (even p) := by
  rw [mem_even_iff hp]
  change p * (U * V - V * U) = (U * V - V * U) * p
  simp only [mul_sub, sub_mul, ← mul_assoc p U, ← mul_assoc p V,
    left_upper hp, left_lower hp, zero_mul, sub_zero]
  rw [mul_assoc U V p, mul_assoc V U p, right_lower hp, right_upper hp, mul_zero, sub_zero]

/-- Conjugation by the reflection reverses the full odd operator. -/
theorem reflection_conjugate_sum : S * (U + V) * S = -(U + V) := by
  have ho : U + V ∈ LinearMap.range (odd p) :=
    (mem_odd_iff hp).mpr (opposite_sum_tangent hp a b)
  have h := odd_anticommutes_reflection hp ho
  have heq : S * (U + V) = -((U + V) * S) := eq_neg_of_add_eq_zero_left h
  rw [heq, neg_mul, mul_assoc, reflection_sq hp, mul_one]

theorem lie_sq_eq_jordan_sq : K ^ 2 = J ^ 2 := by
  have hc := even_commutes_reflection hp (jordan_mem_even hp a b)
  rw [← reflection_mul_jordan hp a b, pow_two, pow_two]
  calc
    (S * J) * (S * J) = S * (J * S) * J := by simp only [mul_assoc]
    _ = S * (S * J) * J := by rw [hc.eq]
    _ = J * J := by rw [← mul_assoc S S J, reflection_sq hp, one_mul]

/-- The odd operator anticommutes with the signed quadratic operator. -/
theorem sum_anticommutes_lie : (U + V) * K + K * (U + V) = 0 := by
  have hu : U * U = 0 := peirceCorner_sq_eq_zero (complement_mul_idempotent p hp.eq)
  have hv : V * V = 0 := peirceCorner_sq_eq_zero (idempotent_mul_complement p hp.eq)
  change (U + V) * (U * V - V * U) + (U * V - V * U) * (U + V) = 0
  calc
    _ = (U * U) * V - (V * V) * U + U * (V * V) - V * (U * U) := by noncomm_ring
    _ = 0 := by rw [hu, hv]; simp

/-- The signed product solves the inhomogeneous second-order idempotent equation. -/
theorem lie_second_order_boundary : p * K + K * p - K = J := by
  change p * (U * V - V * U) + (U * V - V * U) * p - (U * V - V * U) = J
  simp only [mul_sub, sub_mul, ← mul_assoc p U, ← mul_assoc p V,
    left_upper hp, left_lower hp, zero_mul, sub_zero]
  rw [mul_assoc U V p, mul_assoc V U p, right_lower hp, right_upper hp, mul_zero]
  abel

end InfoGeometry.OperatorAlgebra.PeirceCoupling
