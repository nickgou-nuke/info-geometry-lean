import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace InfoGeometry.Spectrometry.FiniteWeightDispersion

open scoped BigOperators

noncomputable section

variable {Line : Type*} [Fintype Line]

def meanWeight (weights : Line → ℝ) : ℝ :=
  (∑ line, weights line) / Fintype.card Line

def squaredWeightSum (weights : Line → ℝ) : ℝ :=
  ∑ line, weights line ^ 2

def dispersion (weights : Line → ℝ) : ℝ :=
  ∑ line, (weights line - meanWeight weights) ^ 2

def varianceEnvelope (count : ℕ) (support : ℝ) : ℝ :=
  support * (1 - support / count)

theorem dispersion_nonneg (weights : Line → ℝ) :
    0 ≤ dispersion weights :=
  Finset.sum_nonneg (fun line _ => sq_nonneg (weights line - meanWeight weights))

theorem dispersion_eq_zero_iff (weights : Line → ℝ) :
    dispersion weights = 0 ↔ ∀ line, weights line = meanWeight weights := by
  rw [dispersion, Finset.sum_eq_zero_iff_of_nonneg (fun line _ => sq_nonneg _)]
  simp only [Finset.mem_univ, true_implies, sq_eq_zero_iff, sub_eq_zero]

theorem dispersion_eq [Nonempty Line] (weights : Line → ℝ) :
    dispersion weights =
      squaredWeightSum weights - (∑ line, weights line) ^ 2 / Fintype.card Line := by
  have count_ne : (Fintype.card Line : ℝ) ≠ 0 :=
    ne_of_gt (Nat.cast_pos.mpr Fintype.card_pos)
  have expansion (line : Line) :
      (weights line - meanWeight weights) ^ 2 =
        weights line ^ 2 - 2 * meanWeight weights * weights line + meanWeight weights ^ 2 := by
    ring
  unfold dispersion
  simp_rw [expansion]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  unfold meanWeight squaredWeightSum
  field_simp [count_ne]
  ring

theorem squared_weight_sum_ge_mean_square [Nonempty Line] (weights : Line → ℝ) :
    (∑ line, weights line) ^ 2 / Fintype.card Line ≤ squaredWeightSum weights := by
  have nonnegative := dispersion_nonneg weights
  rw [dispersion_eq] at nonnegative
  linarith

theorem squared_weight_sum_eq_mean_square_iff [Nonempty Line] (weights : Line → ℝ) :
    squaredWeightSum weights = (∑ line, weights line) ^ 2 / Fintype.card Line ↔
      ∀ line, weights line = meanWeight weights := by
  rw [← dispersion_eq_zero_iff, dispersion_eq, sub_eq_zero]

theorem envelope_completion_of_square (count : ℕ) (support : ℝ)
    (count_pos : 0 < count) :
    varianceEnvelope count support =
      (count : ℝ) / 4 - (support - (count : ℝ) / 2) ^ 2 / count := by
  have count_ne : (count : ℝ) ≠ 0 := ne_of_gt (Nat.cast_pos.mpr count_pos)
  unfold varianceEnvelope
  field_simp [count_ne]
  ring

theorem envelope_le_quarter (count : ℕ) (support : ℝ) (count_pos : 0 < count) :
    varianceEnvelope count support ≤ (count : ℝ) / 4 := by
  rw [envelope_completion_of_square count support count_pos]
  exact sub_le_self _ (div_nonneg (sq_nonneg _) (Nat.cast_nonneg count))

theorem envelope_eq_quarter_iff (count : ℕ) (support : ℝ) (count_pos : 0 < count) :
    varianceEnvelope count support = (count : ℝ) / 4 ↔ support = (count : ℝ) / 2 := by
  have count_ne : (count : ℝ) ≠ 0 := ne_of_gt (Nat.cast_pos.mpr count_pos)
  rw [envelope_completion_of_square count support count_pos]
  simp [sub_eq_self, div_eq_zero_iff, count_ne, sub_eq_zero]

end

end InfoGeometry.Spectrometry.FiniteWeightDispersion
