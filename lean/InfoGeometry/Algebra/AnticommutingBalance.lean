/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib

namespace InfoGeometry.Algebra.AnticommutingBalance

variable {Carrier : Type*} [Ring Carrier] [Algebra ℝ Carrier]

theorem weighted_square (first second : Carrier) (firstWeight secondWeight : ℝ)
    (anticommute : first * second + second * first = 0) :
    (firstWeight • first + secondWeight • second) ^ 2 =
      firstWeight ^ 2 • (first * first) + secondWeight ^ 2 • (second * second) := by
  have reversed : first * second = -(second * first) :=
    eq_neg_of_add_eq_zero_left anticommute
  simp only [pow_two, add_mul, mul_add, smul_mul_smul, reversed, smul_neg]
  module

theorem weighted_square_of_equal_squares (first second : Carrier)
    (firstWeight secondWeight : ℝ)
    (anticommute : first * second + second * first = 0)
    (equalSquares : first * first = second * second) :
    (firstWeight • first + secondWeight • second) ^ 2 =
      (firstWeight ^ 2 + secondWeight ^ 2) • (first * first) := by
  rw [weighted_square first second firstWeight secondWeight anticommute,
    ← equalSquares, add_smul]

theorem complementary_weight_identity (weight : ℝ) :
    weight ^ 2 + (1 - weight) ^ 2 = 1 / 2 + 2 * (weight - 1 / 2) ^ 2 := by
  ring

theorem complementary_weight_minimum (weight : ℝ) :
    1 / 2 ≤ weight ^ 2 + (1 - weight) ^ 2 := by
  rw [complementary_weight_identity]
  nlinarith [sq_nonneg (weight - 1 / 2)]

theorem complementary_weight_minimum_iff (weight : ℝ) :
    weight ^ 2 + (1 - weight) ^ 2 = 1 / 2 ↔ weight = 1 / 2 := by
  rw [complementary_weight_identity]
  constructor
  · intro equality
    have squareZero : (weight - 1 / 2) ^ 2 = 0 := by linarith
    exact sub_eq_zero.mp (sq_eq_zero_iff.mp squareZero)
  · intro equality
    rw [equality]
    norm_num

theorem balanced_square (first second : Carrier)
    (anticommute : first * second + second * first = 0)
    (equalSquares : first * first = second * second) :
    ((1 / 2 : ℝ) • first + (1 / 2 : ℝ) • second) ^ 2 =
      (1 / 2 : ℝ) • (first * first) := by
  rw [weighted_square_of_equal_squares first second (1 / 2) (1 / 2)
    anticommute equalSquares]
  norm_num

theorem balanced_square_ne_zero (first second : Carrier)
    (anticommute : first * second + second * first = 0)
    (equalSquares : first * first = second * second)
    (squareNonzero : first * first ≠ 0) :
    ((1 / 2 : ℝ) • first + (1 / 2 : ℝ) • second) ^ 2 ≠ 0 := by
  rw [balanced_square first second anticommute equalSquares]
  exact smul_ne_zero (by norm_num) squareNonzero

end InfoGeometry.Algebra.AnticommutingBalance

namespace InfoGeometry.Algebra.QHeisenberg

variable {Carrier : Type*} [Ring Carrier]

/-- The commutator readout of a left-scaled exchange relation. -/
theorem q_commutator_readout (q X Y : Carrier)
    (h : X * Y = q * (Y * X)) :
    X * Y - Y * X = (q - 1) * (Y * X) := by
  rw [h]
  noncomm_ring

/-- The anticommutator readout of a left-scaled exchange relation. -/
theorem q_anticommutator_readout (q X Y : Carrier)
    (h : X * Y = q * (Y * X)) :
    X * Y + Y * X = (q + 1) * (Y * X) := by
  rw [h]
  noncomm_ring

/-- The division-free commutator--anticommutator identity induced by
`X * Y = q * (Y * X)`. -/
theorem q_commutator_anticommutator_relation (q X Y : Carrier)
    (h : X * Y = q * (Y * X)) :
    (q + 1) * (X * Y - Y * X) =
      (q - 1) * (X * Y + Y * X) := by
  rw [h]
  noncomm_ring

/-- At `q = 1`, the exchange relation has zero commutator. -/
theorem q_one_commutator_zero (X Y : Carrier)
    (h : X * Y = (1 : Carrier) * (Y * X)) :
    X * Y - Y * X = 0 := by
  simpa using q_commutator_readout (1 : Carrier) X Y h

/-- At `q = -1`, the exchange relation has zero anticommutator. -/
theorem q_neg_one_anticommutator_zero (X Y : Carrier)
    (h : X * Y = (-1 : Carrier) * (Y * X)) :
    X * Y + Y * X = 0 := by
  simpa using q_anticommutator_readout (-1 : Carrier) X Y h

end InfoGeometry.Algebra.QHeisenberg
