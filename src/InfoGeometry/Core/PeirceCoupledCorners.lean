/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Core.PeirceStarCharges

/-!
# Coupling arbitrary opposite Peirce corners

The two inputs are independent elements of the existing directed corner sets.
Their sum is odd, while its square and the bracket of the corners are even.
Reflection interchanges the latter two operators. No commutation, star,
nonvanishing, or cancellation of two is required for the ring identities.
-/

namespace InfoGeometry.Core.PeirceCoupledCorners

open PeirceDecomposition PeirceGrading PeirceStarCharges

variable {A : Type*} [Ring A] {p u v : A}

theorem left_support10 (hp : IsIdempotentElem p) (hu : u ∈ peirce10 p) :
    p * u = u := by
  rcases hu with ⟨a, rfl⟩
  exact peirceCorner_absorb_left hp.eq

theorem right_support10 (hp : IsIdempotentElem p) (hu : u ∈ peirce10 p) :
    u * p = 0 := by
  rcases hu with ⟨a, rfl⟩
  change (p * a * (1 - p)) * p = 0
  rw [mul_assoc, hp.one_sub_mul_self, mul_zero]

theorem left_support01 (hp : IsIdempotentElem p) (hv : v ∈ peirce01 p) :
    p * v = 0 := by
  rcases hv with ⟨b, rfl⟩
  change p * ((1 - p) * b * p) = 0
  calc
    _ = (p * (1 - p)) * b * p := by noncomm_ring
    _ = 0 := by rw [hp.mul_one_sub_self, zero_mul, zero_mul]

theorem right_support01 (hp : IsIdempotentElem p) (hv : v ∈ peirce01 p) :
    v * p = v := by
  rcases hv with ⟨b, rfl⟩
  exact peirceCorner_absorb_right hp.eq

theorem component10_fixed (hp : IsIdempotentElem p) (hu : u ∈ peirce10 p) :
    component10 p u = u := by
  change p * u * (1 - p) = u
  rw [left_support10 hp hu, mul_sub, mul_one, right_support10 hp hu, sub_zero]

theorem component01_fixed (hp : IsIdempotentElem p) (hv : v ∈ peirce01 p) :
    component01 p v = v := by
  change (1 - p) * v * p = v
  rw [sub_mul, one_mul, left_support01 hp hv, sub_zero, right_support01 hp hv]

theorem component10_coupled (hp : IsIdempotentElem p)
    (hu : u ∈ peirce10 p) (hv : v ∈ peirce01 p) :
    component10 p (u + v) = u := by
  change p * (u + v) * (1 - p) = u
  rw [mul_add, left_support10 hp hu, left_support01 hp hv, add_zero,
    mul_sub, mul_one, right_support10 hp hu, sub_zero]

theorem component01_coupled (hp : IsIdempotentElem p)
    (hu : u ∈ peirce10 p) (hv : v ∈ peirce01 p) :
    component01 p (u + v) = v := by
  change (1 - p) * (u + v) * p = v
  calc
    _ = (1 - p) * (u * p + v * p) := by noncomm_ring
    _ = v := by
      rw [right_support10 hp hu, right_support01 hp hv, zero_add,
        sub_mul, one_mul, left_support01 hp hv, sub_zero]

theorem odd_coupled (hp : IsIdempotentElem p)
    (hu : u ∈ peirce10 p) (hv : v ∈ peirce01 p) :
    odd p (u + v) = u + v := by
  rw [odd_apply]
  change component10 p (u + v) + component01 p (u + v) = u + v
  rw [component10_coupled hp hu hv, component01_coupled hp hu hv]

theorem coupled_odd (hp : IsIdempotentElem p)
    (hu : u ∈ peirce10 p) (hv : v ∈ peirce01 p) :
    u + v ∈ LinearMap.range (odd p) := by
  rw [LinearMap.IsIdempotentElem.mem_range_iff (odd_idempotent hp)]
  exact odd_coupled hp hu hv

/-- The square expansion is inherited from the existing odd-square owner. -/
theorem coupled_square (hp : IsIdempotentElem p)
    (hu : u ∈ peirce10 p) (hv : v ∈ peirce01 p) :
    (u + v) ^ 2 = u * v + v * u := by
  calc
    _ = (odd p (u + v)) ^ 2 := by rw [odd_coupled hp hu hv]
    _ = component10 p (u + v) * component01 p (u + v) +
        component01 p (u + v) * component10 p (u + v) := odd_square hp (u + v)
    _ = _ := by rw [component10_coupled hp hu hv, component01_coupled hp hu hv]

theorem left_jordan (hp : IsIdempotentElem p)
    (hu : u ∈ peirce10 p) (hv : v ∈ peirce01 p) :
    p * (u * v + v * u) = u * v := by
  calc
    _ = p * u * v + p * v * u := by noncomm_ring
    _ = _ := by rw [left_support10 hp hu, left_support01 hp hv, zero_mul, add_zero]

theorem right_jordan (hp : IsIdempotentElem p)
    (hu : u ∈ peirce10 p) (hv : v ∈ peirce01 p) :
    (u * v + v * u) * p = u * v := by
  calc
    _ = u * (v * p) + v * (u * p) := by noncomm_ring
    _ = _ := by rw [right_support01 hp hv, right_support10 hp hu, mul_zero, add_zero]

theorem left_bracket (hp : IsIdempotentElem p)
    (hu : u ∈ peirce10 p) (hv : v ∈ peirce01 p) :
    p * ⁅u, v⁆ = u * v := by
  change p * (u * v - v * u) = u * v
  calc
    _ = p * u * v - p * v * u := by noncomm_ring
    _ = _ := by rw [left_support10 hp hu, left_support01 hp hv, zero_mul, sub_zero]

theorem right_bracket (hp : IsIdempotentElem p)
    (hu : u ∈ peirce10 p) (hv : v ∈ peirce01 p) :
    ⁅u, v⁆ * p = u * v := by
  change (u * v - v * u) * p = u * v
  calc
    _ = u * (v * p) - v * (u * p) := by noncomm_ring
    _ = _ := by rw [right_support01 hp hv, right_support10 hp hu, mul_zero, sub_zero]

theorem component11_jordan (hp : IsIdempotentElem p)
    (hu : u ∈ peirce10 p) (hv : v ∈ peirce01 p) :
    component11 p (u * v + v * u) = u * v := by
  change p * (u * v + v * u) * p = u * v
  rw [left_jordan hp hu hv, mul_assoc, right_support01 hp hv]

theorem component00_jordan (hp : IsIdempotentElem p)
    (hu : u ∈ peirce10 p) (hv : v ∈ peirce01 p) :
    component00 p (u * v + v * u) = v * u := by
  change (1 - p) * (u * v + v * u) * (1 - p) = v * u
  rw [sub_mul, one_mul, left_jordan hp hu hv]
  have h : u * v + v * u - u * v = v * u := by abel
  rw [h, mul_sub, mul_one, mul_assoc, right_support10 hp hu, mul_zero, sub_zero]

theorem component11_bracket (hp : IsIdempotentElem p)
    (hu : u ∈ peirce10 p) (hv : v ∈ peirce01 p) :
    component11 p ⁅u, v⁆ = u * v := by
  change p * ⁅u, v⁆ * p = u * v
  rw [left_bracket hp hu hv, mul_assoc, right_support01 hp hv]

theorem component00_bracket (hp : IsIdempotentElem p)
    (hu : u ∈ peirce10 p) (hv : v ∈ peirce01 p) :
    component00 p ⁅u, v⁆ = -(v * u) := by
  change (1 - p) * ⁅u, v⁆ * (1 - p) = -(v * u)
  rw [sub_mul, one_mul, left_bracket hp hu hv]
  have h : ⁅u, v⁆ - u * v = -(v * u) := by
    change (u * v - v * u) - u * v = -(v * u)
    abel
  rw [h, neg_mul, mul_sub, mul_one, mul_assoc,
    right_support10 hp hu, mul_zero, sub_zero]

theorem jordan_mem_even (hp : IsIdempotentElem p)
    (hu : u ∈ peirce10 p) (hv : v ∈ peirce01 p) :
    u * v + v * u ∈ LinearMap.range (even p) := by
  rw [mem_even_iff hp, left_jordan hp hu hv, right_jordan hp hu hv]

theorem bracket_mem_even (hp : IsIdempotentElem p)
    (hu : u ∈ peirce10 p) (hv : v ∈ peirce01 p) :
    ⁅u, v⁆ ∈ LinearMap.range (even p) := by
  rw [mem_even_iff hp, left_bracket hp hu hv, right_bracket hp hu hv]

theorem reflection_mul_jordan (hp : IsIdempotentElem p)
    (hu : u ∈ peirce10 p) (hv : v ∈ peirce01 p) :
    reflection p * (u * v + v * u) = ⁅u, v⁆ := by
  change (2 * p - 1) * (u * v + v * u) = u * v - v * u
  simp only [sub_mul, one_mul, two_mul, add_mul, left_jordan hp hu hv]
  abel

theorem reflection_mul_bracket (hp : IsIdempotentElem p)
    (hu : u ∈ peirce10 p) (hv : v ∈ peirce01 p) :
    reflection p * ⁅u, v⁆ = u * v + v * u := by
  rw [← reflection_mul_jordan hp hu hv, ← mul_assoc, reflection_sq hp, one_mul]

theorem jordan_eq_zero_iff_bracket_eq_zero (hp : IsIdempotentElem p)
    (hu : u ∈ peirce10 p) (hv : v ∈ peirce01 p) :
    u * v + v * u = 0 ↔ ⁅u, v⁆ = 0 := by
  constructor
  · intro h
    rw [← reflection_mul_jordan hp hu hv, h, mul_zero]
  · intro h
    rw [← reflection_mul_bracket hp hu hv, h, mul_zero]

theorem jordan_eq_zero_iff_products (hp : IsIdempotentElem p)
    (hu : u ∈ peirce10 p) (hv : v ∈ peirce01 p) :
    u * v + v * u = 0 ↔ u * v = 0 ∧ v * u = 0 := by
  constructor
  · intro h
    constructor
    · have hh := congrArg (component11 p) h
      rw [component11_jordan hp hu hv] at hh
      simpa only [component11, mul_zero, zero_mul] using hh
    · have hh := congrArg (component00 p) h
      rw [component00_jordan hp hu hv] at hh
      simpa only [component00, mul_zero, zero_mul] using hh
  · rintro ⟨h₁, h₂⟩
    rw [h₁, h₂, zero_add]

theorem coupled_eq_zero_iff (hp : IsIdempotentElem p)
    (hu : u ∈ peirce10 p) (hv : v ∈ peirce01 p) :
    u + v = 0 ↔ u = 0 ∧ v = 0 := by
  constructor
  · intro h
    have hu0 := congrArg (fun x => p * x) h
    rw [mul_add, left_support10 hp hu, left_support01 hp hv, add_zero, mul_zero] at hu0
    exact ⟨hu0, by simpa only [hu0, zero_add] using h⟩
  · rintro ⟨rfl, rfl⟩
    exact zero_add 0

theorem coupled_conjugation (hp : IsIdempotentElem p)
    (hu : u ∈ peirce10 p) (hv : v ∈ peirce01 p) :
    reflection p * (u + v) * reflection p = -(u + v) := by
  have h := odd_anticommutes_reflection hp (coupled_odd hp hu hv)
  rw [eq_neg_of_add_eq_zero_left h, neg_mul, mul_assoc, reflection_sq hp, mul_one]

theorem jordan_conjugation (hp : IsIdempotentElem p)
    (hu : u ∈ peirce10 p) (hv : v ∈ peirce01 p) :
    reflection p * (u * v + v * u) * reflection p = u * v + v * u := by
  have h := even_commutes_reflection hp (jordan_mem_even hp hu hv)
  rw [h.eq, mul_assoc, reflection_sq hp, mul_one]

theorem bracket_conjugation (hp : IsIdempotentElem p)
    (hu : u ∈ peirce10 p) (hv : v ∈ peirce01 p) :
    reflection p * ⁅u, v⁆ * reflection p = ⁅u, v⁆ := by
  have h := even_commutes_reflection hp (bracket_mem_even hp hu hv)
  rw [h.eq, mul_assoc, reflection_sq hp, mul_one]

section Star

variable [StarRing A]

/-- Taking the star exchanges corners without requiring self-adjoint input. -/
theorem star_component10 (hp : IsSelfAdjoint p) (a : A) :
    star (component10 p a) = component01 p (star a) := by
  simp only [component10, component01, complementIdempotent, star_mul,
    star_sub, star_one, hp.star_eq, mul_assoc]

theorem star_mem_peirce01 (hp : IsSelfAdjoint p) (hu : u ∈ peirce10 p) :
    star u ∈ peirce01 p := by
  rcases hu with ⟨a, rfl⟩
  change star (component10 p a) ∈ peirce01 p
  rw [star_component10 hp]
  exact component01_mem p (star a)

end Star

end InfoGeometry.Core.PeirceCoupledCorners
