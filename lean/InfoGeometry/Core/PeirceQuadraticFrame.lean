/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Core.PeirceCoupledCorners

/-!
# The quadratic frame of independent opposite Peirce corners

All operators remain elements of the original associative ring. The sum and
difference of the two corners have opposite squares, and their product gives
the corner bracket. The common quadratic operator commutes with the specified
generators. The multiplication and iterated-bracket identities retain that
operator as a factor; no normalization or cancellation of two is used.

The final section states exact product and square rules for any reciprocal
inner-commutator cycle, independently of an idempotent or a Peirce decomposition.
-/

namespace InfoGeometry.Core.PeirceQuadraticFrame

open PeirceDecomposition PeirceGrading PeirceStarCharges PeirceCoupledCorners

attribute [local instance 100] LieRing.ofAssociativeRing

variable {A : Type*} [Ring A]

section OppositeCorners

variable {p u v : A}

/-- The difference square is the existing commutator-square identity. -/
theorem difference_square (hp : IsIdempotentElem p)
    (hu : u ∈ peirce10 p) (hv : v ∈ peirce01 p) :
    (u - v) ^ 2 = -(u * v + v * u) := by
  have h := commutator_square hp (u + v)
  rw [commutator_eq_corners, component10_coupled hp hu hv,
    component01_coupled hp hu hv, odd_coupled hp hu hv,
    coupled_square hp hu hv] at h
  exact h

/-- The sum and difference anticommute in the ambient ring. -/
theorem sum_difference_anticommute (hp : IsIdempotentElem p)
    (hu : u ∈ peirce10 p) (hv : v ∈ peirce01 p) :
    (u + v) * (u - v) + (u - v) * (u + v) = 0 := by
  have h := commutator_odd_anticommute hp (u + v)
  rw [commutator_eq_corners, component10_coupled hp hu hv,
    component01_coupled hp hu hv, odd_coupled hp hu hv] at h
  simpa only [add_comm] using h

/-- The ordered product of difference and sum is the native corner bracket. -/
theorem bracket_eq_difference_mul_sum (hp : IsIdempotentElem p)
    (hu : u ∈ peirce10 p) (hv : v ∈ peirce01 p) :
    ⁅u, v⁆ = (u - v) * (u + v) := by
  have hu2 : u ^ 2 = 0 := by
    have h := (corners_sq_zero hp u).1
    change (component10 p u) ^ 2 = 0 at h
    simpa only [component10_fixed hp hu] using h
  have hv2 : v ^ 2 = 0 := by
    have h := (corners_sq_zero hp v).2
    change (component01 p v) ^ 2 = 0 at h
    simpa only [component01_fixed hp hv] using h
  calc
    ⁅u, v⁆ = u * v - v * u := rfl
    _ = u ^ 2 + (u * v - v * u) - v ^ 2 := by
      rw [hu2, hv2, zero_add, sub_zero]
    _ = (u - v) * (u + v) := by noncomm_ring

/-- Reversing the ordered factors changes the sign. -/
theorem bracket_eq_neg_sum_mul_difference (hp : IsIdempotentElem p)
    (hu : u ∈ peirce10 p) (hv : v ∈ peirce01 p) :
    ⁅u, v⁆ = -((u + v) * (u - v)) := by
  rw [bracket_eq_difference_mul_sum hp hu hv]
  apply eq_neg_of_add_eq_zero_left
  simpa only [add_comm] using sum_difference_anticommute hp hu hv

/-- Reflection duality gives the square of the corner bracket without reflexivity. -/
theorem bracket_square (hp : IsIdempotentElem p)
    (hu : u ∈ peirce10 p) (hv : v ∈ peirce01 p) :
    ⁅u, v⁆ ^ 2 = (u * v + v * u) ^ 2 := by
  have h := even_commutes_reflection hp (jordan_mem_even hp hu hv)
  rw [← reflection_mul_jordan hp hu hv, h.mul_pow 2,
    pow_two (reflection p), reflection_sq hp, one_mul]

/-- Only the first generator's corner hypothesis is needed for this centralizer. -/
theorem quadratic_commute_left (hp : IsIdempotentElem p)
    (hu : u ∈ peirce10 p) :
    Commute (u * v + v * u) u := by
  have hu2 : u * u = 0 := by
    have h := (corners_sq_zero hp u).1
    change (component10 p u) ^ 2 = 0 at h
    simpa only [component10_fixed hp hu, pow_two] using h
  change (u * v + v * u) * u = u * (u * v + v * u)
  calc
    _ = u * v * u + v * (u * u) := by noncomm_ring
    _ = (u * u) * v + u * (v * u) := by
      simp only [hu2, mul_zero, zero_mul, add_zero, zero_add, mul_assoc]
    _ = _ := by noncomm_ring

/-- Only the second generator's corner hypothesis is needed for this centralizer. -/
theorem quadratic_commute_right (hp : IsIdempotentElem p)
    (hv : v ∈ peirce01 p) :
    Commute (u * v + v * u) v := by
  have hv2 : v * v = 0 := by
    have h := (corners_sq_zero hp v).2
    change (component01 p v) ^ 2 = 0 at h
    simpa only [component01_fixed hp hv, pow_two] using h
  change (u * v + v * u) * v = v * (u * v + v * u)
  calc
    _ = u * (v * v) + v * u * v := by noncomm_ring
    _ = v * (u * v) + (v * v) * u := by
      simp only [hv2, mul_zero, zero_mul, add_zero, zero_add, mul_assoc]
    _ = _ := by noncomm_ring

theorem quadratic_commute_sum (hp : IsIdempotentElem p)
    (hu : u ∈ peirce10 p) (hv : v ∈ peirce01 p) :
    Commute (u * v + v * u) (u + v) :=
  (quadratic_commute_left hp hu).add_right (quadratic_commute_right hp hv)

theorem quadratic_commute_difference (hp : IsIdempotentElem p)
    (hu : u ∈ peirce10 p) (hv : v ∈ peirce01 p) :
    Commute (u * v + v * u) (u - v) :=
  (quadratic_commute_left hp hu).sub_right (quadratic_commute_right hp hv)

theorem quadratic_commute_bracket (hp : IsIdempotentElem p)
    (hu : u ∈ peirce10 p) (hv : v ∈ peirce01 p) :
    Commute (u * v + v * u) ⁅u, v⁆ := by
  change Commute (u * v + v * u) (u * v - v * u)
  have h₁ := quadratic_commute_left (v := v) hp hu
  have h₂ := quadratic_commute_right (u := u) hp hv
  exact (h₁.mul_right h₂).sub_right (h₂.mul_right h₁)

/-- The quadratic factor is retained in the bracket-times-sum product. -/
theorem bracket_mul_sum (hp : IsIdempotentElem p)
    (hu : u ∈ peirce10 p) (hv : v ∈ peirce01 p) :
    ⁅u, v⁆ * (u + v) = (u * v + v * u) * (u - v) := by
  calc
    _ = (u - v) * ((u + v) ^ 2) := by
      rw [bracket_eq_difference_mul_sum hp hu hv]
      noncomm_ring
    _ = (u - v) * (u * v + v * u) := by rw [coupled_square hp hu hv]
    _ = _ := (quadratic_commute_difference hp hu hv).eq.symm

/-- The quadratic factor is retained in the bracket-times-difference product. -/
theorem bracket_mul_difference (hp : IsIdempotentElem p)
    (hu : u ∈ peirce10 p) (hv : v ∈ peirce01 p) :
    ⁅u, v⁆ * (u - v) = (u * v + v * u) * (u + v) := by
  calc
    _ = -((u + v) * ((u - v) ^ 2)) := by
      rw [bracket_eq_neg_sum_mul_difference hp hu hv]
      noncomm_ring
    _ = (u + v) * (u * v + v * u) := by
      rw [difference_square hp hu hv, mul_neg, neg_neg]
    _ = _ := (quadratic_commute_sum hp hu hv).eq.symm

theorem bracket_sum_anticommute (hp : IsIdempotentElem p)
    (hu : u ∈ peirce10 p) (hv : v ∈ peirce01 p) :
    ⁅u, v⁆ * (u + v) + (u + v) * ⁅u, v⁆ = 0 := by
  calc
    _ = ((u + v) * (u - v) + (u - v) * (u + v)) * (u + v) := by
      rw [bracket_eq_difference_mul_sum hp hu hv]
      noncomm_ring
    _ = 0 := by rw [sum_difference_anticommute hp hu hv, zero_mul]

theorem bracket_difference_anticommute (hp : IsIdempotentElem p)
    (hu : u ∈ peirce10 p) (hv : v ∈ peirce01 p) :
    ⁅u, v⁆ * (u - v) + (u - v) * ⁅u, v⁆ = 0 := by
  calc
    _ = (u - v) * ((u + v) * (u - v) + (u - v) * (u + v)) := by
      rw [bracket_eq_difference_mul_sum hp hu hv]
      noncomm_ring
    _ = 0 := by rw [sum_difference_anticommute hp hu hv, mul_zero]

theorem bracket_bracket_sum (hp : IsIdempotentElem p)
    (hu : u ∈ peirce10 p) (hv : v ∈ peirce01 p) :
    ⁅⁅u, v⁆, u + v⁆ = 2 • ((u * v + v * u) * (u - v)) := by
  have h : (u + v) * ⁅u, v⁆ = -(⁅u, v⁆ * (u + v)) := by
    apply eq_neg_of_add_eq_zero_left
    simpa only [add_comm] using bracket_sum_anticommute hp hu hv
  rw [Ring.lie_def, h, sub_neg_eq_add, bracket_mul_sum hp hu hv, two_nsmul]

theorem bracket_bracket_difference (hp : IsIdempotentElem p)
    (hu : u ∈ peirce10 p) (hv : v ∈ peirce01 p) :
    ⁅⁅u, v⁆, u - v⁆ = 2 • ((u * v + v * u) * (u + v)) := by
  have h : (u - v) * ⁅u, v⁆ = -(⁅u, v⁆ * (u - v)) := by
    apply eq_neg_of_add_eq_zero_left
    simpa only [add_comm] using bracket_difference_anticommute hp hu hv
  rw [Ring.lie_def, h, sub_neg_eq_add, bracket_mul_difference hp hu hv, two_nsmul]

/-- The inner action of the corner bracket factors through the quadratic operator. -/
theorem quadratic_bracket_left_factor (hp : IsIdempotentElem p)
    (hu : u ∈ peirce10 p) (hv : v ∈ peirce01 p) (x : A) :
    ⁅⁅u, v⁆, (u * v + v * u) * x⁆ = (u * v + v * u) * ⁅⁅u, v⁆, x⁆ := by
  have h := (quadratic_commute_bracket hp hu hv).symm
  change ⁅u, v⁆ * ((u * v + v * u) * x) -
      ((u * v + v * u) * x) * ⁅u, v⁆ =
    (u * v + v * u) * (⁅u, v⁆ * x - x * ⁅u, v⁆)
  rw [← mul_assoc ⁅u, v⁆ (u * v + v * u) x, h.eq]
  noncomm_ring

/-- The second inner action retains the square of the quadratic operator. -/
theorem double_bracket_sum (hp : IsIdempotentElem p)
    (hu : u ∈ peirce10 p) (hv : v ∈ peirce01 p) :
    ⁅⁅u, v⁆, ⁅⁅u, v⁆, u + v⁆⁆ =
      4 • ((u * v + v * u) ^ 2 * (u + v)) := by
  rw [bracket_bracket_sum hp hu hv, lie_nsmul,
    quadratic_bracket_left_factor hp hu hv, bracket_bracket_difference hp hu hv]
  simp only [nsmul_eq_mul, Nat.cast_ofNat]
  noncomm_ring

theorem double_bracket_difference (hp : IsIdempotentElem p)
    (hu : u ∈ peirce10 p) (hv : v ∈ peirce01 p) :
    ⁅⁅u, v⁆, ⁅⁅u, v⁆, u - v⁆⁆ =
      4 • ((u * v + v * u) ^ 2 * (u - v)) := by
  rw [bracket_bracket_difference hp hu hv, lie_nsmul,
    quadratic_bracket_left_factor hp hu hv, bracket_bracket_sum hp hu hv]
  simp only [nsmul_eq_mul, Nat.cast_ofNat]
  noncomm_ring

end OppositeCorners

section ReciprocalCycle

variable (a e j : A)

/-- Leibniz applied to the ordered product in an arbitrary reciprocal cycle. -/
theorem reciprocal_product_bracket (he : ⁅a, e⁆ = j) (hj : ⁅a, j⁆ = e) :
    ⁅a, j * e⁆ = e ^ 2 + j ^ 2 := by
  calc
    _ = ⁅a, j⁆ * e + j * ⁅a, e⁆ := by
      simp only [Ring.lie_def]
      noncomm_ring
    _ = e ^ 2 + j ^ 2 := by rw [hj, he]; noncomm_ring

theorem reciprocal_reverse_product_bracket (he : ⁅a, e⁆ = j) (hj : ⁅a, j⁆ = e) :
    ⁅a, e * j⁆ = j ^ 2 + e ^ 2 := by
  calc
    _ = ⁅a, e⁆ * j + e * ⁅a, j⁆ := by
      simp only [Ring.lie_def]
      noncomm_ring
    _ = j ^ 2 + e ^ 2 := by rw [he, hj]; noncomm_ring

/-- Differentiating a square gives the anticommutator, without division by two. -/
theorem reciprocal_left_square_bracket (he : ⁅a, e⁆ = j) :
    ⁅a, e ^ 2⁆ = j * e + e * j := by
  calc
    _ = ⁅a, e⁆ * e + e * ⁅a, e⁆ := by
      simp only [Ring.lie_def]
      noncomm_ring
    _ = j * e + e * j := by rw [he]

theorem reciprocal_right_square_bracket (hj : ⁅a, j⁆ = e) :
    ⁅a, j ^ 2⁆ = e * j + j * e := by
  calc
    _ = ⁅a, j⁆ * j + j * ⁅a, j⁆ := by
      simp only [Ring.lie_def]
      noncomm_ring
    _ = e * j + j * e := by rw [hj]

/-- Constancy of the ordered product is exactly the opposite-square equation. -/
theorem reciprocal_product_bracket_eq_zero_iff (he : ⁅a, e⁆ = j) (hj : ⁅a, j⁆ = e) :
    ⁅a, j * e⁆ = 0 ↔ e ^ 2 = -(j ^ 2) := by
  rw [reciprocal_product_bracket a e j he hj]
  constructor
  · exact eq_neg_of_add_eq_zero_left
  · intro h
    rw [h, neg_add_cancel]

/-- Constancy of the square is exactly anticommutation in a reciprocal cycle. -/
theorem reciprocal_square_bracket_eq_zero_iff (he : ⁅a, e⁆ = j) :
    ⁅a, e ^ 2⁆ = 0 ↔ j * e + e * j = 0 := by
  rw [reciprocal_left_square_bracket a e j he]

theorem reciprocal_product_commute_iff (he : ⁅a, e⁆ = j) (hj : ⁅a, j⁆ = e) :
    Commute a (j * e) ↔ e ^ 2 = -(j ^ 2) := by
  rw [commute_iff_lie_eq, reciprocal_product_bracket_eq_zero_iff a e j he hj]

theorem reciprocal_square_commute_iff (he : ⁅a, e⁆ = j) :
    Commute a (e ^ 2) ↔ j * e + e * j = 0 := by
  rw [commute_iff_lie_eq, reciprocal_square_bracket_eq_zero_iff a e j he]

end ReciprocalCycle

end InfoGeometry.Core.PeirceQuadraticFrame
