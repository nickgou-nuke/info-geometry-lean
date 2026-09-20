import InfoGeometry.Algebra.ZornVectorMatrix
import InfoGeometry.Canonical.RenyiFiniteOrderReadback

namespace InfoGeometry.Quantum.ZornDiagonalPurity

open InfoGeometry.Algebra
open InfoGeometry.Algebra.ZornVectorMatrix
open InfoGeometry.Canonical.RenyiFiniteOrderReadback
open scoped BigOperators

noncomputable section

theorem weighted_idempotents (weight : ℝ) :
    weight • (E11 : ZornVectorMatrix ℝ) + (1 - weight) • E22 =
      diagonal weight (1 - weight) := by
  ext coordinate <;> simp [E11, E22, diagonal]

theorem diagonal_trace_normalized (weight : ℝ) :
    trace (diagonal weight (1 - weight)) = 1 := by
  rw [trace_diagonal]
  ring

theorem diagonal_trace_square_completed_square (weight : ℝ) :
    trace (mul (diagonal weight (1 - weight)) (diagonal weight (1 - weight))) =
      1 / 2 + 2 * (weight - 1 / 2) ^ 2 := by
  rw [trace_diagonal_mul_diagonal]
  ring

theorem diagonal_trace_square_lower_bound (weight : ℝ) :
    1 / 2 ≤ trace
      (mul (diagonal weight (1 - weight)) (diagonal weight (1 - weight))) := by
  rw [diagonal_trace_square_completed_square]
  nlinarith [sq_nonneg (weight - 1 / 2)]

theorem diagonal_trace_square_eq_half_iff (weight : ℝ) :
    trace (mul (diagonal weight (1 - weight)) (diagonal weight (1 - weight))) =
      1 / 2 ↔ weight = 1 / 2 := by
  rw [diagonal_trace_square_completed_square]
  constructor
  · intro equality
    have square_zero : (weight - 1 / 2) ^ 2 = 0 := by linarith
    exact sub_eq_zero.mp (sq_eq_zero_iff.mp square_zero)
  · rintro rfl
    norm_num

theorem diagonal_trace_square_upper_bound (weight : ℝ)
    (nonnegative : 0 ≤ weight) (at_most_one : weight ≤ 1) :
    trace (mul (diagonal weight (1 - weight)) (diagonal weight (1 - weight))) ≤ 1 := by
  rw [trace_diagonal_mul_diagonal]
  nlinarith [mul_nonneg nonnegative (sub_nonneg.mpr at_most_one)]

theorem equipartition_square :
    mul (diagonal (1 / 2 : ℝ) (1 / 2)) (diagonal (1 / 2) (1 / 2)) =
      diagonal (1 / 4) (1 / 4) := by
  rw [diagonal_mul_diagonal]
  norm_num

theorem equipartition_trace_square :
    trace (mul (diagonal (1 / 2 : ℝ) (1 / 2)) (diagonal (1 / 2) (1 / 2))) =
      1 / 2 := by
  rw [equipartition_square, trace_diagonal]
  norm_num

theorem equipartition_renyi_two :
    renyiTwo (fun _ : Fin 2 => (1 / 2 : ℝ)) = Real.log 2 := by
  rw [renyiTwo_eq_neg_log_collision]
  have collision : (∑ index : Fin 2, (1 / 2 : ℝ) ^ 2) = 1 / 2 := by
    norm_num
  rw [collision, one_div, Real.log_inv, neg_neg]

end

end InfoGeometry.Quantum.ZornDiagonalPurity
