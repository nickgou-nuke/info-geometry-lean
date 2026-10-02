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
