import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

noncomputable section

namespace InfoGeometry.InformationGeometry.BurgStein

def d1F (x : ℝ) : ℝ :=
  - x⁻¹

def d2F (x : ℝ) : ℝ :=
  x⁻¹ ^ 2

def d3F (x : ℝ) : ℝ :=
  - 2 * x⁻¹ ^ 3

theorem log_barrier_self_concordance (x : ℝ) (hx : 0 < x) :
    |d3F x| = 2 * (d2F x) ^ (3 / 2 : ℝ) := by
  dsimp [d3F, d2F]
  have h_x_inv_pos : 0 < x⁻¹ := inv_pos.mpr hx
  have h_abs : |-2 * x⁻¹ ^ 3| = 2 * x⁻¹ ^ 3 := by
    rw [abs_mul, abs_neg, abs_two]
    have h_pow_pos : 0 ≤ x⁻¹ ^ 3 := by positivity
    rw [abs_of_nonneg h_pow_pos]
  rw [h_abs]
  have h_pow_law : ((x⁻¹ ^ 2) : ℝ) ^ (3 / 2 : ℝ) = x⁻¹ ^ 3 := by
    have h_nonneg : 0 ≤ x⁻¹ := le_of_lt h_x_inv_pos
    rw [← Real.rpow_natCast, ← Real.rpow_mul h_nonneg]
    have h_mul : ((2 : ℕ) : ℝ) * (3 / 2 : ℝ) = 3 := by norm_num
    rw [h_mul]
    exact Real.rpow_natCast (x⁻¹) 3
  rw [h_pow_law]

def fisherScaleMetric (x v : ℝ) : ℝ :=
  (v / x) ^ 2

theorem hessian_eq_fisherScaleMetric (x v : ℝ) :
    d2F x * v ^ 2 = fisherScaleMetric x v := by
  dsimp [d2F, fisherScaleMetric]
  rw [div_pow]
  ring

def steinScalar (x y : ℝ) : ℝ :=
  x / y - Real.log (x / y) - 1

def bipartiteStein (x y : ℝ × ℝ) : ℝ :=
  steinScalar x.1 y.1 + steinScalar x.2 y.2

theorem bipartiteStein_eq_sum (x y : ℝ × ℝ) :
    bipartiteStein x y = steinScalar x.1 y.1 + steinScalar x.2 y.2 := rfl

theorem bipartiteStein_nonneg (x y : ℝ × ℝ)
    (hx1 : 0 < x.1) (hy1 : 0 < y.1)
    (hx2 : 0 < x.2) (hy2 : 0 < y.2) :
    0 ≤ bipartiteStein x y := by
  dsimp [bipartiteStein, steinScalar]
  have h_u1 : 0 < x.1 / y.1 := div_pos hx1 hy1
  have h_u2 : 0 < x.2 / y.2 := div_pos hx2 hy2
  have h_log1 := Real.log_le_sub_one_of_pos h_u1
  have h_log2 := Real.log_le_sub_one_of_pos h_u2
  linarith

end InfoGeometry.InformationGeometry.BurgStein

end noncomputable section
