/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.EmergentGeometry.HarmonicRectangle

namespace InfoGeometry.EmergentGeometry.HarmonicRectangle

noncomputable section

/-- Real part of a complex quadratic, including its affine terms. -/
def harmonicQuadratic (a b c : ℂ) (z : ℂ) : ℝ := (a * z ^ 2 + b * z + c).re

theorem harmonicQuadratic_harmonic (a b c z : ℂ) :
    InnerProductSpace.HarmonicAt (harmonicQuadratic a b c) z := by
  exact (((analyticAt_const.mul (analyticAt_id.pow 2)).add
    (analyticAt_const.mul analyticAt_id)).add analyticAt_const).harmonicAt_re

theorem harmonicQuadratic_coordinates (a b c : ℂ) (x y : ℝ) :
    harmonicQuadratic a b c ⟨x, y⟩ =
      -a.re * y ^ 2 + (-2 * a.im * x - b.im) * y +
        (a.re * x ^ 2 + b.re * x + c.re) := by
  simp [harmonicQuadratic, pow_two, Complex.mul_re, Complex.mul_im]
  ring

/-- Symmetric interval integration removes the odd term, without sign assumptions. -/
theorem symmetric_quadratic_integral (A B C h : ℝ) :
    (∫ x in -h..h, A * x ^ 2 + B * x + C) =
      2 * h * (C + A * h ^ 2 / 3) := by
  have hA : IntervalIntegrable (fun x : ℝ => A * x ^ 2)
      MeasureTheory.volume (-h) h :=
    (continuous_const.mul (continuous_id.pow 2)).intervalIntegrable _ _
  have hB : IntervalIntegrable (fun x : ℝ => B * x)
      MeasureTheory.volume (-h) h :=
    (continuous_const.mul continuous_id).intervalIntegrable _ _
  rw [intervalIntegral.integral_add (hA.add hB)
    (continuous_const.intervalIntegrable _ _), intervalIntegral.integral_add hA hB]
  have hlinear : (∫ x in -h..h, B * x) = 0 := by
    rw [intervalIntegral.integral_const_mul B (fun x : ℝ => x), integral_id]
    ring
  rw [hlinear]
  simp only [intervalIntegral.integral_const_mul, integral_pow,
    intervalIntegral.integral_const, smul_eq_mul]
  ring

theorem harmonicQuadratic_vertical_integral (a b c : ℂ) (x h : ℝ) :
    (∫ y in -h..h, harmonicQuadratic a b c ⟨x, y⟩) =
      2 * h * (a.re * x ^ 2 + b.re * x + c.re - a.re * h ^ 2 / 3) := by
  simp_rw [harmonicQuadratic_coordinates]
  rw [symmetric_quadratic_integral]
  ring

theorem harmonicQuadratic_rectangleIntegral (a b c : ℂ) (w h : ℝ) :
    rectangleIntegral (harmonicQuadratic a b c) w h =
      (4 * w * h) * (c.re + a.re * (w ^ 2 - h ^ 2) / 3) := by
  unfold rectangleIntegral
  simp_rw [harmonicQuadratic_vertical_integral]
  rw [intervalIntegral.integral_const_mul]
  have heq : (fun x : ℝ => a.re * x ^ 2 + b.re * x + c.re - a.re * h ^ 2 / 3) =
      (fun x : ℝ => a.re * x ^ 2 + b.re * x + (c.re - a.re * h ^ 2 / 3)) := by
    funext x; ring
  rw [heq, symmetric_quadratic_integral]
  ring

theorem harmonicQuadratic_rectangle_average (a b c : ℂ) {w h : ℝ}
    (hw : 0 < w) (hh : 0 < h) :
    rectangleIntegral (harmonicQuadratic a b c) w h / (4 * w * h) =
      c.re + a.re * (w ^ 2 - h ^ 2) / 3 := by
  rw [harmonicQuadratic_rectangleIntegral]
  exact mul_div_cancel_left₀ _ (mul_ne_zero (mul_ne_zero (by norm_num) hw.ne') hh.ne')

theorem harmonicQuadratic_center_mean_iff (a b c : ℂ) {w h : ℝ}
    (hw : 0 < w) (hh : 0 < h) :
    rectangleIntegral (harmonicQuadratic a b c) w h / (4 * w * h) =
      harmonicQuadratic a b c 0 ↔ a.re = 0 ∨ w = h := by
  rw [harmonicQuadratic_rectangle_average a b c hw hh]
  simp only [harmonicQuadratic, zero_pow (by decide : (2 : ℕ) ≠ 0),
    mul_zero, zero_add]
  constructor
  · intro heq
    have hp : a.re * (w ^ 2 - h ^ 2) = 0 := by linarith
    rcases mul_eq_zero.mp hp with ha | hs
    · exact Or.inl ha
    · right; nlinarith
  · rintro (ha | rfl)
    · rw [ha]; ring
    · ring

end
end InfoGeometry.EmergentGeometry.HarmonicRectangle
