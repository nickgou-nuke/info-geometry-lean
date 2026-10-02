import InfoGeometry.Algebra.MoebiusTraceInvariant
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

noncomputable section

namespace InfoGeometry.Algebra.MoebiusDiagonalPolar

open MoebiusTraceInvariant

def polarParameter (radius angle : ℝ) : ℂ :=
  ⟨radius * Real.cos angle, radius * Real.sin angle⟩

theorem polarParameter_mul_reciprocal (radius angle : ℝ) (hradius : radius ≠ 0) :
    polarParameter radius angle * polarParameter radius⁻¹ (-angle) = 1 := by
  ext
  · simp only [polarParameter, Complex.mul_re, Complex.one_re, Real.cos_neg, Real.sin_neg]
    calc
      radius * Real.cos angle * (radius⁻¹ * Real.cos angle) -
          radius * Real.sin angle * (radius⁻¹ * -Real.sin angle) =
          (radius * radius⁻¹) * (Real.cos angle ^ 2 + Real.sin angle ^ 2) := by ring
      _ = 1 := by rw [mul_inv_cancel₀ hradius, Real.cos_sq_add_sin_sq]; simp
  · simp only [polarParameter, Complex.mul_im, Complex.one_im, Real.cos_neg, Real.sin_neg]
    ring

theorem polarParameter_ne_zero (radius angle : ℝ) (hradius : radius ≠ 0) :
    polarParameter radius angle ≠ 0 := by
  intro hzero
  have hproduct := polarParameter_mul_reciprocal radius angle hradius
  rw [hzero, zero_mul] at hproduct
  exact zero_ne_one hproduct

theorem polarParameter_inv (radius angle : ℝ) (hradius : radius ≠ 0) :
    (polarParameter radius angle)⁻¹ = polarParameter radius⁻¹ (-angle) := by
  exact inv_eq_of_mul_eq_one_right (polarParameter_mul_reciprocal radius angle hradius)

theorem diagonal_discriminant_factorization (parameter : ℂ) :
    Matrix.trace (diagonalRepresentative parameter) ^ 2 -
      4 * (diagonalRepresentative parameter).det = (parameter - parameter⁻¹) ^ 2 := by
  simp [diagonalRepresentative, Matrix.trace, Fin.sum_univ_two, Matrix.det_fin_two] <;> ring

theorem polar_trace (radius angle : ℝ) (hradius : radius ≠ 0) :
    Matrix.trace (diagonalRepresentative (polarParameter radius angle)) =
      ⟨(radius + radius⁻¹) * Real.cos angle,
        (radius - radius⁻¹) * Real.sin angle⟩ := by
  simp only [diagonalRepresentative, Matrix.trace, Fin.sum_univ_two,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  change polarParameter radius angle + (polarParameter radius angle)⁻¹ = _
  rw [polarParameter_inv radius angle hradius]
  ext <;> simp [polarParameter] <;> ring

theorem polar_traceRatio_sub_four_im (radius angle : ℝ) (hradius : radius ≠ 0) :
    (traceRatio (diagonalRepresentative (polarParameter radius angle)) - 4).im =
      (radius ^ 2 - (radius⁻¹) ^ 2) * Real.sin (2 * angle) := by
  rw [traceRatio, diagonalRepresentative_det _ (polarParameter_ne_zero radius angle hradius),
    div_one, polar_trace radius angle hradius]
  simp [pow_two, Complex.mul_im, Real.sin_two_mul] <;> ring

theorem polar_traceRatio_nonreal (radius angle : ℝ) (hradius : 1 < radius)
    (hangle : Real.sin (2 * angle) ≠ 0) :
    (traceRatio (diagonalRepresentative (polarParameter radius angle)) - 4).im ≠ 0 := by
  have hpositive : 0 < radius := lt_trans zero_lt_one hradius
  have hinverse : radius⁻¹ < 1 := (inv_lt_one₀ hpositive).2 hradius
  have hinverse_nonnegative : 0 ≤ radius⁻¹ := le_of_lt (inv_pos.mpr hpositive)
  have hcoefficient : 0 < radius ^ 2 - (radius⁻¹) ^ 2 := by nlinarith
  rw [polar_traceRatio_sub_four_im radius angle (ne_of_gt hpositive)]
  exact mul_ne_zero (ne_of_gt hcoefficient) hangle

end InfoGeometry.Algebra.MoebiusDiagonalPolar
