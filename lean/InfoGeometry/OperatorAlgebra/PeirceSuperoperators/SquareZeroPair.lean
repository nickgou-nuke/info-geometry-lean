/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Tactic.NoncommRing

/-!
# Operator-weighted commutator cycles

Two square-zero elements give opposite squares and an anticommuting pair.
Their commutator exchanges that pair with the operator weight `u*v + v*u`.
There is no scalar normalization or inverse hypothesis.
-/

namespace InfoGeometry.OperatorAlgebra.PeirceSuperoperators

variable {A : Type*} [Ring A]

theorem square_zero_pair_sum_sq {u v : A} (hu : u * u = 0) (hv : v * v = 0) :
    (u + v) * (u + v) = u * v + v * u := by
  noncomm_ring [hu, hv]

theorem square_zero_pair_sub_sq {u v : A} (hu : u * u = 0) (hv : v * v = 0) :
    (u - v) * (u - v) = -(u * v + v * u) := by
  noncomm_ring [hu, hv]

theorem square_zero_pair_sub_mul_sum {u v : A} (hu : u * u = 0) (hv : v * v = 0) :
    (u - v) * (u + v) = ⁅u, v⁆ := by
  simp only [Ring.lie_def]
  noncomm_ring [hu, hv]

theorem square_zero_pair_sum_mul_sub {u v : A} (hu : u * u = 0) (hv : v * v = 0) :
    (u + v) * (u - v) = -⁅u, v⁆ := by
  simp only [Ring.lie_def]
  noncomm_ring [hu, hv]

/-- The first exchange retains the full, generally noncentral operator weight. -/
theorem weighted_lie_sum {u v : A} (hu : u * u = 0) (hv : v * v = 0) :
    ⁅⁅u, v⁆, u + v⁆ = 2 • ((u * v + v * u) * (u - v)) := by
  have huu (x : A) : u * (u * x) = 0 := by rw [← mul_assoc, hu, zero_mul]
  have hvv (x : A) : v * (v * x) = 0 := by rw [← mul_assoc, hv, zero_mul]
  simp only [Ring.lie_def, two_nsmul]
  noncomm_ring [hu, hv, huu, hvv]

theorem weighted_lie_sub {u v : A} (hu : u * u = 0) (hv : v * v = 0) :
    ⁅⁅u, v⁆, u - v⁆ = 2 • ((u * v + v * u) * (u + v)) := by
  have huu (x : A) : u * (u * x) = 0 := by rw [← mul_assoc, hu, zero_mul]
  have hvv (x : A) : v * (v * x) = 0 := by rw [← mul_assoc, hv, zero_mul]
  simp only [Ring.lie_def, two_nsmul]
  noncomm_ring [hu, hv, huu, hvv]

theorem weighted_lie_twice_sum {u v : A} (hu : u * u = 0) (hv : v * v = 0) :
    ⁅⁅u, v⁆, ⁅⁅u, v⁆, u + v⁆⁆ =
      4 • ((u * v + v * u) ^ 2 * (u + v)) := by
  have huu (x : A) : u * (u * x) = 0 := by rw [← mul_assoc, hu, zero_mul]
  have hvv (x : A) : v * (v * x) = 0 := by rw [← mul_assoc, hv, zero_mul]
  rw [weighted_lie_sum hu hv]
  simp only [Ring.lie_def, two_nsmul, show (4 : ℕ) = 2 + 2 from rfl,
    add_nsmul, pow_two]
  noncomm_ring [hu, hv, huu, hvv]

theorem weighted_lie_twice_sub {u v : A} (hu : u * u = 0) (hv : v * v = 0) :
    ⁅⁅u, v⁆, ⁅⁅u, v⁆, u - v⁆⁆ =
      4 • ((u * v + v * u) ^ 2 * (u - v)) := by
  have huu (x : A) : u * (u * x) = 0 := by rw [← mul_assoc, hu, zero_mul]
  have hvv (x : A) : v * (v * x) = 0 := by rw [← mul_assoc, hv, zero_mul]
  rw [weighted_lie_sub hu hv]
  simp only [Ring.lie_def, two_nsmul, show (4 : ℕ) = 2 + 2 from rfl,
    add_nsmul, pow_two]
  noncomm_ring [hu, hv, huu, hvv]

/-- Leibniz gives the exact obstruction to conserving the product in an inner two-cycle. -/
theorem inner_cycle_product (p c e : A) (hc : ⁅p, c⁆ = e) (he : ⁅p, e⁆ = c) :
    ⁅p, c * e⁆ = e * e + c * c := by
  calc
    _ = ⁅p, c⁆ * e + c * ⁅p, e⁆ := by simp only [Ring.lie_def]; noncomm_ring
    _ = _ := by rw [hc, he]

theorem inner_cycle_square (p c e : A) (he : ⁅p, e⁆ = c) :
    ⁅p, e * e⁆ = c * e + e * c := by
  calc
    _ = ⁅p, e⁆ * e + e * ⁅p, e⁆ := by simp only [Ring.lie_def]; noncomm_ring
    _ = _ := by rw [he]

theorem inner_cycle_product_conserved_iff (p c e : A)
    (hc : ⁅p, c⁆ = e) (he : ⁅p, e⁆ = c) :
    ⁅p, c * e⁆ = 0 ↔ c * c = -(e * e) := by
  rw [inner_cycle_product p c e hc he, add_comm, add_eq_zero_iff_eq_neg]

theorem inner_cycle_square_conserved_iff (p c e : A) (he : ⁅p, e⁆ = c) :
    ⁅p, e * e⁆ = 0 ↔ c * e = -(e * c) := by
  rw [inner_cycle_square p c e he, add_eq_zero_iff_eq_neg]

end InfoGeometry.OperatorAlgebra.PeirceSuperoperators
