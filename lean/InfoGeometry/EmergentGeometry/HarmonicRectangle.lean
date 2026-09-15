import InfoGeometry.EmergentGeometry.HarmonicMeanValue
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic

namespace InfoGeometry.EmergentGeometry.HarmonicRectangle

noncomputable section

def quadraticHarmonic (point : ℂ) : ℝ := (point ^ 2).re

theorem quadraticHarmonic_harmonic (point : ℂ) :
    InnerProductSpace.HarmonicAt quadraticHarmonic point := by
  exact (show AnalyticAt ℂ (fun value : ℂ => value ^ 2) point from
    analyticAt_id.pow 2).harmonicAt_re

theorem quadraticHarmonic_coordinates (horizontal vertical : ℝ) :
    quadraticHarmonic ⟨horizontal, vertical⟩ = horizontal ^ 2 - vertical ^ 2 := by
  simp [quadraticHarmonic, pow_two, Complex.mul_re]

def rectangleIntegral (field : ℂ → ℝ) (halfWidth halfHeight : ℝ) : ℝ :=
  ∫ horizontal in -halfWidth..halfWidth,
    ∫ vertical in -halfHeight..halfHeight, field ⟨horizontal, vertical⟩

theorem quadraticHarmonic_vertical_integral (horizontal halfHeight : ℝ) :
    (∫ vertical in -halfHeight..halfHeight,
      quadraticHarmonic ⟨horizontal, vertical⟩) =
      2 * halfHeight * horizontal ^ 2 - 2 * halfHeight ^ 3 / 3 := by
  simp_rw [quadraticHarmonic_coordinates]
  have constant_integrable : IntervalIntegrable (fun _ : ℝ => horizontal ^ 2)
      MeasureTheory.volume (-halfHeight) halfHeight := continuous_const.intervalIntegrable _ _
  have square_integrable : IntervalIntegrable (fun vertical : ℝ => vertical ^ 2)
      MeasureTheory.volume (-halfHeight) halfHeight :=
    (continuous_id.pow 2).intervalIntegrable _ _
  rw [intervalIntegral.integral_sub constant_integrable square_integrable]
  rw [integral_pow]
  simp only [intervalIntegral.integral_const, smul_eq_mul]
  ring

theorem quadraticHarmonic_rectangleIntegral (halfWidth halfHeight : ℝ) :
    rectangleIntegral quadraticHarmonic halfWidth halfHeight =
      (4 * halfWidth * halfHeight) * (halfWidth ^ 2 - halfHeight ^ 2) / 3 := by
  unfold rectangleIntegral
  simp_rw [quadraticHarmonic_vertical_integral]
  have square_integrable : IntervalIntegrable
      (fun horizontal : ℝ => 2 * halfHeight * horizontal ^ 2)
      MeasureTheory.volume (-halfWidth) halfWidth :=
    (continuous_const.mul (continuous_id.pow 2)).intervalIntegrable _ _
  have constant_integrable : IntervalIntegrable (fun _ : ℝ => 2 * halfHeight ^ 3 / 3)
      MeasureTheory.volume (-halfWidth) halfWidth := continuous_const.intervalIntegrable _ _
  rw [intervalIntegral.integral_sub square_integrable constant_integrable]
  rw [intervalIntegral.integral_const_mul, integral_pow]
  simp only [intervalIntegral.integral_const, smul_eq_mul]
  ring

theorem quadraticHarmonic_rectangle_average (halfWidth halfHeight : ℝ)
    (width_positive : 0 < halfWidth) (height_positive : 0 < halfHeight) :
    rectangleIntegral quadraticHarmonic halfWidth halfHeight /
        (4 * halfWidth * halfHeight) = (halfWidth ^ 2 - halfHeight ^ 2) / 3 := by
  rw [quadraticHarmonic_rectangleIntegral]
  field_simp

theorem quadraticHarmonic_center_mean_iff_square (halfWidth halfHeight : ℝ)
    (width_positive : 0 < halfWidth) (height_positive : 0 < halfHeight) :
    rectangleIntegral quadraticHarmonic halfWidth halfHeight /
        (4 * halfWidth * halfHeight) = quadraticHarmonic 0 ↔ halfWidth = halfHeight := by
  rw [quadraticHarmonic_rectangle_average halfWidth halfHeight width_positive height_positive]
  simp only [quadraticHarmonic, zero_pow (by norm_num : (2 : ℕ) ≠ 0), Complex.zero_re]
  constructor
  · intro equality
    have equal_squares : halfWidth ^ 2 = halfHeight ^ 2 := by linarith
    nlinarith
  · rintro rfl
    simp

theorem harmonic_rectangle_counterexample :
    ∃ field : ℂ → ℝ, (∀ point, InnerProductSpace.HarmonicAt field point) ∧
      rectangleIntegral field 2 1 ≠ (4 * 2 * 1 : ℝ) * field 0 := by
  refine ⟨quadraticHarmonic, quadraticHarmonic_harmonic, ?_⟩
  norm_num [quadraticHarmonic_rectangleIntegral, quadraticHarmonic]

theorem quadraticHarmonic_circleAverage (radius : ℝ) :
    Real.circleAverage quadraticHarmonic 0 radius = 0 := by
  have harmonic : InnerProductSpace.HarmonicOnNhd quadraticHarmonic
      (Metric.closedBall 0 |radius|) := fun point _ => quadraticHarmonic_harmonic point
  simpa [quadraticHarmonic] using HarmonicOnNhd.circleAverage_eq harmonic

end

end InfoGeometry.EmergentGeometry.HarmonicRectangle
