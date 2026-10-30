/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.PeirceSuperoperators.SquareZeroPair

/-!
# Adjoint-square actions of a square-zero pair

For square-zero elements `u` and `v`, the expressions `u + v`, `u - v`,
`u * v + v * u`, and `⁅u, v⁆` carry exact actions of three native linear
endomorphisms. The coefficients retain the full left operator weight
`u * v + v * u`. Its commutation with the two generators is proved from
square-zero hypotheses; ambient centrality is not assumed.

First-order bracket identities precede the endomorphism action table.
The final endomorphism identity holds on the whole algebra without any
square-zero hypothesis. No characteristic or invertibility assumption is
needed, and all integer coefficients below are natural repeated addition.
-/

namespace InfoGeometry.OperatorAlgebra.SquareZeroModeActions

attribute [local instance 100] LieRing.ofAssociativeRing

open InfoGeometry.OperatorAlgebra.PeirceSuperoperators

variable {A : Type*} [Ring A]

private theorem square_zero_nested (u : A) (hu : u * u = 0) (z : A) :
    u * (u * z) = 0 := by
  rw [← mul_assoc, hu, zero_mul]

/-- The weight commutes with the first generator from that generator's
square-zero equation alone. -/
theorem left_lie_weight {u v : A} (hu : u * u = 0) :
    ⁅u, u * v + v * u⁆ = 0 := by
  simp only [Ring.lie_def]
  noncomm_ring [hu, square_zero_nested u hu]

/-- The analogous conservation identity for the second generator. -/
theorem right_lie_weight {u v : A} (hv : v * v = 0) :
    ⁅v, u * v + v * u⁆ = 0 := by
  simp only [Ring.lie_def]
  noncomm_ring [hv, square_zero_nested v hv]

theorem sum_lie_weight {u v : A} (hu : u * u = 0) (hv : v * v = 0) :
    ⁅u + v, u * v + v * u⁆ = 0 := by
  simp only [add_lie, left_lie_weight hu, right_lie_weight hv, add_zero]

theorem difference_lie_weight {u v : A}
    (hu : u * u = 0) (hv : v * v = 0) :
    ⁅u - v, u * v + v * u⁆ = 0 := by
  simp only [sub_lie, left_lie_weight hu, right_lie_weight hv, sub_self]

/-- The sum and difference have this bracket in every associative ring. -/
theorem sum_lie_difference (u v : A) :
    ⁅u + v, u - v⁆ = -(2 • ⁅u, v⁆) := by
  simp only [Ring.lie_def, two_nsmul]
  noncomm_ring

theorem difference_lie_sum (u v : A) :
    ⁅u - v, u + v⁆ = 2 • ⁅u, v⁆ := by
  simp only [Ring.lie_def, two_nsmul]
  noncomm_ring

/-- Reverse the existing weighted commutator cycle without replacing its
operator weight by a scalar. -/
theorem sum_lie_bracket {u v : A} (hu : u * u = 0) (hv : v * v = 0) :
    ⁅u + v, ⁅u, v⁆⁆ = -(2 • ((u * v + v * u) * (u - v))) := by
  calc
    _ = -⁅⁅u, v⁆, u + v⁆ := (lie_skew (u + v) ⁅u, v⁆).symm
    _ = _ := by rw [weighted_lie_sum hu hv]

theorem difference_lie_bracket {u v : A}
    (hu : u * u = 0) (hv : v * v = 0) :
    ⁅u - v, ⁅u, v⁆⁆ = -(2 • ((u * v + v * u) * (u + v))) := by
  calc
    _ = -⁅⁅u, v⁆, u - v⁆ := (lie_skew (u - v) ⁅u, v⁆).symm
    _ = _ := by rw [weighted_lie_sub hu hv]

/-- A conserved left coefficient factors out of a commutator. -/
theorem lie_mul_of_lie_eq_zero {a m : A} (h : ⁅a, m⁆ = 0) (z : A) :
    ⁅a, m * z⁆ = m * ⁅a, z⁆ := by
  calc
    _ = ⁅a, m⁆ * z + m * ⁅a, z⁆ := by
      simp only [Ring.lie_def]
      noncomm_ring
    _ = _ := by rw [h, zero_mul, zero_add]

section LinearActions

variable {R : Type*} [CommRing R] [Algebra R A]

/-- The negative adjoint square of the sum annihilates the weight. -/
theorem neg_ad_sum_sq_weight {u v : A}
    (hu : u * u = 0) (hv : v * v = 0) :
    (-((LieAlgebra.ad R A (u + v)) ^ 2)) (u * v + v * u) = 0 := by
  simp only [pow_two]
  change -⁅u + v, ⁅u + v, u * v + v * u⁆⁆ = 0
  rw [sum_lie_weight hu hv, lie_zero, neg_zero]

/-- The negative adjoint square of the sum annihilates the sum. -/
theorem neg_ad_sum_sq_sum (u v : A) :
    (-((LieAlgebra.ad R A (u + v)) ^ 2)) (u + v) = 0 := by
  simp only [pow_two]
  change -⁅u + v, ⁅u + v, u + v⁆⁆ = 0
  rw [lie_self, lie_zero, neg_zero]

theorem neg_ad_sum_sq_difference {u v : A}
    (hu : u * u = 0) (hv : v * v = 0) :
    (-((LieAlgebra.ad R A (u + v)) ^ 2)) (u - v) =
      -(4 • ((u * v + v * u) * (u - v))) := by
  simp only [pow_two]
  change -⁅u + v, ⁅u + v, u - v⁆⁆ =
    -(4 • ((u * v + v * u) * (u - v)))
  rw [sum_lie_difference, lie_neg, lie_nsmul, sum_lie_bracket hu hv]
  simp only [two_nsmul, show (4 : ℕ) = 2 + 2 from rfl, add_nsmul]
  noncomm_ring

theorem neg_ad_sum_sq_bracket {u v : A}
    (hu : u * u = 0) (hv : v * v = 0) :
    (-((LieAlgebra.ad R A (u + v)) ^ 2)) ⁅u, v⁆ =
      -(4 • ((u * v + v * u) * ⁅u, v⁆)) := by
  simp only [pow_two]
  change -⁅u + v, ⁅u + v, ⁅u, v⁆⁆⁆ =
    -(4 • ((u * v + v * u) * ⁅u, v⁆))
  rw [sum_lie_bracket hu hv, lie_neg, lie_nsmul,
    lie_mul_of_lie_eq_zero (sum_lie_weight hu hv) (u - v), sum_lie_difference]
  simp only [two_nsmul, show (4 : ℕ) = 2 + 2 from rfl, add_nsmul]
  noncomm_ring

/-- The adjoint square of the difference annihilates the weight. -/
theorem ad_difference_sq_weight {u v : A}
    (hu : u * u = 0) (hv : v * v = 0) :
    ((LieAlgebra.ad R A (u - v)) ^ 2) (u * v + v * u) = 0 := by
  simp only [pow_two]
  change ⁅u - v, ⁅u - v, u * v + v * u⁆⁆ = 0
  rw [difference_lie_weight hu hv, lie_zero]

/-- The adjoint square of the difference annihilates the difference. -/
theorem ad_difference_sq_difference (u v : A) :
    ((LieAlgebra.ad R A (u - v)) ^ 2) (u - v) = 0 := by
  simp only [pow_two]
  change ⁅u - v, ⁅u - v, u - v⁆⁆ = 0
  rw [lie_self, lie_zero]

theorem ad_difference_sq_sum {u v : A}
    (hu : u * u = 0) (hv : v * v = 0) :
    ((LieAlgebra.ad R A (u - v)) ^ 2) (u + v) =
      -(4 • ((u * v + v * u) * (u + v))) := by
  simp only [pow_two]
  change ⁅u - v, ⁅u - v, u + v⁆⁆ =
    -(4 • ((u * v + v * u) * (u + v)))
  rw [difference_lie_sum, lie_nsmul, difference_lie_bracket hu hv]
  simp only [two_nsmul, show (4 : ℕ) = 2 + 2 from rfl, add_nsmul]
  noncomm_ring

theorem ad_difference_sq_bracket {u v : A}
    (hu : u * u = 0) (hv : v * v = 0) :
    ((LieAlgebra.ad R A (u - v)) ^ 2) ⁅u, v⁆ =
      -(4 • ((u * v + v * u) * ⁅u, v⁆)) := by
  simp only [pow_two]
  change ⁅u - v, ⁅u - v, ⁅u, v⁆⁆⁆ =
    -(4 • ((u * v + v * u) * ⁅u, v⁆))
  rw [difference_lie_bracket hu hv, lie_neg, lie_nsmul,
    lie_mul_of_lie_eq_zero (difference_lie_weight hu hv) (u + v), difference_lie_sum]
  simp only [two_nsmul, show (4 : ℕ) = 2 + 2 from rfl, add_nsmul]
  noncomm_ring

/-- The symmetric mixed adjoint operator annihilates the weight. -/
theorem neg_ad_symmetric_weight {u v : A}
    (hu : u * u = 0) (hv : v * v = 0) :
    (-(LieAlgebra.ad R A u * LieAlgebra.ad R A v +
      LieAlgebra.ad R A v * LieAlgebra.ad R A u)) (u * v + v * u) = 0 := by
  change -(⁅u, ⁅v, u * v + v * u⁆⁆ + ⁅v, ⁅u, u * v + v * u⁆⁆) = 0
  rw [right_lie_weight hv, left_lie_weight hu, lie_zero, lie_zero,
    add_zero, neg_zero]

theorem neg_ad_symmetric_sum {u v : A}
    (hu : u * u = 0) (hv : v * v = 0) :
    (-(LieAlgebra.ad R A u * LieAlgebra.ad R A v +
      LieAlgebra.ad R A v * LieAlgebra.ad R A u)) (u + v) =
      -(2 • ((u * v + v * u) * (u + v))) := by
  change -(⁅u, ⁅v, u + v⁆⁆ + ⁅v, ⁅u, u + v⁆⁆) =
    -(2 • ((u * v + v * u) * (u + v)))
  simp only [Ring.lie_def, two_nsmul]
  noncomm_ring [hu, hv, square_zero_nested u hu, square_zero_nested v hv]

theorem neg_ad_symmetric_difference {u v : A}
    (hu : u * u = 0) (hv : v * v = 0) :
    (-(LieAlgebra.ad R A u * LieAlgebra.ad R A v +
      LieAlgebra.ad R A v * LieAlgebra.ad R A u)) (u - v) =
      -(2 • ((u * v + v * u) * (u - v))) := by
  change -(⁅u, ⁅v, u - v⁆⁆ + ⁅v, ⁅u, u - v⁆⁆) =
    -(2 • ((u * v + v * u) * (u - v)))
  simp only [Ring.lie_def, two_nsmul]
  noncomm_ring [hu, hv, square_zero_nested u hu, square_zero_nested v hv]

theorem neg_ad_symmetric_bracket {u v : A}
    (hu : u * u = 0) (hv : v * v = 0) :
    (-(LieAlgebra.ad R A u * LieAlgebra.ad R A v +
      LieAlgebra.ad R A v * LieAlgebra.ad R A u)) ⁅u, v⁆ =
      -(4 • ((u * v + v * u) * ⁅u, v⁆)) := by
  change -(⁅u, ⁅v, ⁅u, v⁆⁆⁆ + ⁅v, ⁅u, ⁅u, v⁆⁆⁆) =
    -(4 • ((u * v + v * u) * ⁅u, v⁆))
  simp only [Ring.lie_def, show (4 : ℕ) = 2 + 2 from rfl, add_nsmul, two_nsmul]
  noncomm_ring [hu, hv, square_zero_nested u hu, square_zero_nested v hv]

/-- Polarization is an identity of native endomorphisms of the entire
algebra, without a square-zero hypothesis or cancellation of the factor two. -/
theorem ad_sum_difference_polarization (u v : A) :
    -((LieAlgebra.ad R A (u + v)) ^ 2) +
      (LieAlgebra.ad R A (u - v)) ^ 2 =
      -(2 • (LieAlgebra.ad R A u * LieAlgebra.ad R A v +
        LieAlgebra.ad R A v * LieAlgebra.ad R A u)) := by
  ext z
  simp only [pow_two]
  change -⁅u + v, ⁅u + v, z⁆⁆ + ⁅u - v, ⁅u - v, z⁆⁆ =
    -(2 • (⁅u, ⁅v, z⁆⁆ + ⁅v, ⁅u, z⁆⁆))
  simp only [Ring.lie_def, two_nsmul]
  noncomm_ring

end LinearActions

end InfoGeometry.OperatorAlgebra.SquareZeroModeActions
