import InfoGeometry.Arithmetic.AmariZetaDuallyFlatGeometry
import InfoGeometry.Physics.HarishChandraCasimirBridge

namespace InfoGeometry.Spectral.QuadraticParameterReality

open InfoGeometry.Physics.HarishChandraCasimir

theorem casimir_eq_fisher_polynomial (parameter : ℂ) :
    casimirEigenvalue parameter =
      InfoGeometry.Arithmetic.AmariZeta.fisherRaoMetric parameter := rfl

theorem real_part (parameter : ℂ) :
    (casimirEigenvalue parameter).re =
      parameter.re * (1 - parameter.re) + parameter.im ^ 2 := by
  simp [casimirEigenvalue, Complex.mul_re]
  ring

theorem imaginary_part (parameter : ℂ) :
    (casimirEigenvalue parameter).im = parameter.im * (1 - 2 * parameter.re) := by
  simp [casimirEigenvalue, Complex.mul_im]
  ring

theorem real_iff (parameter : ℂ) :
    (casimirEigenvalue parameter).im = 0 ↔
      parameter.re = 1 / 2 ∨ parameter.im = 0 :=
  InfoGeometry.Arithmetic.AmariZeta.fisherRaoMetric_is_real_iff parameter

theorem real_iff_critical_of_im_ne_zero (parameter : ℂ)
    (hnonreal : parameter.im ≠ 0) :
    (casimirEigenvalue parameter).im = 0 ↔ parameter.re = 1 / 2 := by
  rw [real_iff]
  simp [hnonreal]

theorem reflection_eq_conjugate_iff (parameter : ℂ) :
    1 - parameter = star parameter ↔ parameter.re = 1 / 2 := by
  constructor
  · intro hequal
    have hreal := congrArg Complex.re hequal
    simp at hreal
    linarith
  · intro hreal
    apply Complex.ext
    · simp [hreal]
      norm_num
    · simp

theorem real_part_of_critical (parameter : ℂ) (hcritical : parameter.re = 1 / 2) :
    (casimirEigenvalue parameter).re = 1 / 4 + parameter.im ^ 2 := by
  rw [real_part, hcritical]
  ring

theorem critical_lower_bound (parameter : ℂ) (hcritical : parameter.re = 1 / 2) :
    1 / 4 ≤ (casimirEigenvalue parameter).re := by
  rw [real_part_of_critical parameter hcritical]
  exact casimir_spectral_gap parameter.im

theorem critical_minimum_iff (parameter : ℂ) (hcritical : parameter.re = 1 / 2) :
    (casimirEigenvalue parameter).re = 1 / 4 ↔ parameter.im = 0 := by
  rw [real_part_of_critical parameter hcritical]
  constructor
  · intro hequal
    have hsquare : parameter.im ^ 2 = 0 := by linarith
    exact (sq_eq_zero_iff).mp hsquare
  · intro hzero
    simp [hzero]

theorem below_quarter_of_real_off_critical (parameter : ℂ)
    (hreal : parameter.im = 0) (hoff : parameter.re ≠ 1 / 2) :
    (casimirEigenvalue parameter).re < 1 / 4 := by
  rw [real_part, hreal]
  have hpositive := sq_pos_of_ne_zero (sub_ne_zero.mpr hoff)
  nlinarith

theorem reflection_invariant_below_quarter :
    casimirEigenvalue (1 - (1 / 4 : ℂ)) = casimirEigenvalue (1 / 4 : ℂ) ∧
    (casimirEigenvalue (1 / 4 : ℂ)).im = 0 ∧
    (casimirEigenvalue (1 / 4 : ℂ)).re < 1 / 4 := by
  refine ⟨casimirEigenvalue_reflection _, ?_, ?_⟩
  · norm_num [casimirEigenvalue, Complex.mul_im]
  · norm_num [casimirEigenvalue, Complex.mul_re]

end InfoGeometry.Spectral.QuadraticParameterReality
