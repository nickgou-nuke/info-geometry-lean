import Mathlib.Analysis.Complex.Exponential
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic

set_option autoImplicit false

namespace InfoGeometry.Analysis.ModifiedBessel

open Complex Real intervalIntegral

noncomputable section

/-- The order-zero modified Bessel function of the first kind, defined by its standard
angular integral representation

`I₀(z) = (2π)⁻¹ ∫₀^{2π} exp(z cos θ) dθ`.

This definition is valid for complex `z` and does not depend on a surrogate exponential
or an external CAS certificate.
-/
noncomputable def I0 (z : ℂ) : ℂ :=
  (((2 * Real.pi : ℝ) : ℂ)⁻¹) *
    ∫ θ in (0 : ℝ)..(2 * Real.pi), Complex.exp (z * (Real.cos θ : ℂ))

/-- The angular integrand defining `I₀` is interval integrable. -/
theorem intervalIntegrable_I0_integrand (z : ℂ) :
    IntervalIntegrable
      (fun θ : ℝ => Complex.exp (z * (Real.cos θ : ℂ)))
      MeasureTheory.volume 0 (2 * Real.pi) := by
  have hcont : Continuous
      (fun θ : ℝ => Complex.exp (z * (Real.cos θ : ℂ))) := by
    fun_prop
  exact hcont.intervalIntegrable _ _

/-- Exact normalization at the origin. -/
@[simp] theorem I0_zero : I0 0 = 1 := by
  unfold I0
  have hfun :
      (fun θ : ℝ => Complex.exp ((0 : ℂ) * (Real.cos θ : ℂ))) =
        fun _ : ℝ => (1 : ℂ) := by
    funext θ
    simp
  rw [hfun, intervalIntegral.integral_const]
  simp only [sub_zero, Complex.real_smul, mul_one]
  have htwo_pi_real : (2 * Real.pi : ℝ) ≠ 0 :=
    mul_ne_zero (by norm_num) Real.pi_ne_zero
  have htwo_pi_complex : (((2 * Real.pi : ℝ) : ℂ)) ≠ 0 := by
    exact_mod_cast htwo_pi_real
  exact inv_mul_cancel₀ htwo_pi_complex

end
end InfoGeometry.Analysis.ModifiedBessel
