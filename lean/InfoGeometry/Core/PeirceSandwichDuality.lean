/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.LieJordanSandwichGeometry

/-!
# Reflection duality of opposite-corner sandwich operators

The native sums and differences of `LinearMap.mulLeftRight` have the same
kernel and range. Reflection intertwines them on both output and input.
All statements retain the ambient ring and require no cancellation of two.
-/

namespace InfoGeometry.Core.PeirceSandwichDuality

open PeirceDecomposition PeirceGrading PeirceCoupledCorners
open Canonical.LieJordanSandwichGeometry

variable {A : Type*} [Ring A] {p u v : A}

theorem reflection_mul_corner10 (hp : IsIdempotentElem p) (hu : u ∈ peirce10 p) :
    reflection p * u = u := by
  simp only [reflection, sub_mul, two_mul, add_mul, one_mul, left_support10 hp hu]
  abel

theorem reflection_mul_corner01 (hp : IsIdempotentElem p) (hv : v ∈ peirce01 p) :
    reflection p * v = -v := by
  simp only [reflection, sub_mul, two_mul, add_mul, one_mul, left_support01 hp hv]
  abel

theorem corner10_mul_reflection (hp : IsIdempotentElem p) (hu : u ∈ peirce10 p) :
    u * reflection p = -u := by
  simp only [reflection, mul_sub, two_mul, mul_add, mul_one, right_support10 hp hu]
  abel

theorem corner01_mul_reflection (hp : IsIdempotentElem p) (hv : v ∈ peirce01 p) :
    v * reflection p = v := by
  simp only [reflection, mul_sub, two_mul, mul_add, mul_one, right_support01 hp hv]
  abel

theorem reflection_mul_sandwich_sum (hp : IsIdempotentElem p)
    (hu : u ∈ peirce10 p) (hv : v ∈ peirce01 p) (x : A) :
    reflection p * (u * x * v + v * x * u) = u * x * v - v * x * u := by
  simp only [mul_add, ← mul_assoc, reflection_mul_corner10 hp hu,
    reflection_mul_corner01 hp hv, neg_mul, sub_eq_add_neg]

theorem reflection_mul_sandwich_sub (hp : IsIdempotentElem p)
    (hu : u ∈ peirce10 p) (hv : v ∈ peirce01 p) (x : A) :
    reflection p * (u * x * v - v * x * u) = u * x * v + v * x * u := by
  rw [← reflection_mul_sandwich_sum hp hu hv, ← mul_assoc, reflection_sq hp, one_mul]

theorem sandwich_sum_reflection (hp : IsIdempotentElem p)
    (hu : u ∈ peirce10 p) (hv : v ∈ peirce01 p) (x : A) :
    u * (reflection p * x) * v + v * (reflection p * x) * u =
      -(u * x * v - v * x * u) := by
  simp only [← mul_assoc, corner10_mul_reflection hp hu,
    corner01_mul_reflection hp hv, neg_mul]
  abel

theorem sandwich_sub_reflection (hp : IsIdempotentElem p)
    (hu : u ∈ peirce10 p) (hv : v ∈ peirce01 p) (x : A) :
    u * (reflection p * x) * v - v * (reflection p * x) * u =
      -(u * x * v + v * x * u) := by
  simp only [← mul_assoc, corner10_mul_reflection hp hu,
    corner01_mul_reflection hp hv, neg_mul]
  abel

theorem sandwich_sub_mem_even (hp : IsIdempotentElem p)
    (hu : u ∈ peirce10 p) (hv : v ∈ peirce01 p) (x : A) :
    u * x * v - v * x * u ∈ LinearMap.range (even p) := by
  rw [← neg_neg (u * x * v - v * x * u),
    ← sandwich_sum_reflection hp hu hv x]
  exact (LinearMap.range (even p)).neg_mem (sandwich_sum_mem_even hp hu hv _)

theorem sandwich_sub_eq_zero_of_odd (hp : IsIdempotentElem p)
    (hu : u ∈ peirce10 p) (hv : v ∈ peirce01 p)
    {x : A} (hx : x ∈ LinearMap.range (odd p)) :
    u * x * v - v * x * u = 0 := by
  rw [← reflection_mul_sandwich_sum hp hu hv,
    sandwich_sum_eq_zero_of_odd hp hu hv hx, mul_zero]

section LinearMaps

variable {R : Type*} [CommRing R] [Algebra R A]

theorem reflection_mul_sandwich_sum_eq (hp : IsIdempotentElem p)
    (hu : u ∈ peirce10 p) (hv : v ∈ peirce01 p) :
    LinearMap.mulLeft R (reflection p) *
        (LinearMap.mulLeftRight R (u, v) + LinearMap.mulLeftRight R (v, u)) =
      LinearMap.mulLeftRight R (u, v) - LinearMap.mulLeftRight R (v, u) := by
  ext x
  exact reflection_mul_sandwich_sum hp hu hv x

theorem reflection_mul_sandwich_sub_eq (hp : IsIdempotentElem p)
    (hu : u ∈ peirce10 p) (hv : v ∈ peirce01 p) :
    LinearMap.mulLeft R (reflection p) *
        (LinearMap.mulLeftRight R (u, v) - LinearMap.mulLeftRight R (v, u)) =
      LinearMap.mulLeftRight R (u, v) + LinearMap.mulLeftRight R (v, u) := by
  ext x
  exact reflection_mul_sandwich_sub hp hu hv x

theorem sandwich_ker_eq (hp : IsIdempotentElem p)
    (hu : u ∈ peirce10 p) (hv : v ∈ peirce01 p) :
    (LinearMap.mulLeftRight R (u, v) + LinearMap.mulLeftRight R (v, u)).ker =
      (LinearMap.mulLeftRight R (u, v) - LinearMap.mulLeftRight R (v, u)).ker := by
  ext x
  change u * x * v + v * x * u = 0 ↔ u * x * v - v * x * u = 0
  constructor
  · intro h
    rw [← reflection_mul_sandwich_sum hp hu hv, h, mul_zero]
  · intro h
    rw [← reflection_mul_sandwich_sub hp hu hv, h, mul_zero]

theorem sandwich_range_eq (hp : IsIdempotentElem p)
    (hu : u ∈ peirce10 p) (hv : v ∈ peirce01 p) :
    (LinearMap.mulLeftRight R (u, v) + LinearMap.mulLeftRight R (v, u)).range =
      (LinearMap.mulLeftRight R (u, v) - LinearMap.mulLeftRight R (v, u)).range := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    refine ⟨-(reflection p * y), ?_⟩
    rw [map_neg]
    change -(u * (reflection p * y) * v - v * (reflection p * y) * u) = _
    rw [sandwich_sub_reflection hp hu hv, neg_neg]
    rfl
  · rintro ⟨y, rfl⟩
    refine ⟨-(reflection p * y), ?_⟩
    rw [map_neg]
    change -(u * (reflection p * y) * v + v * (reflection p * y) * u) = _
    rw [sandwich_sum_reflection hp hu hv, neg_neg]
    rfl

end LinearMaps

end InfoGeometry.Core.PeirceSandwichDuality
