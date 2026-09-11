import Mathlib.Data.Real.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

/-!
# Modal Damping and Resolvent-Scalar Readout

This module formalizes:
1. **A scalar contractive multiplier**:
   The reciprocal denominator below is bounded algebraically for positive
   damping; no infinite geometric series is defined here.
2. **A damped cosine mode**:
   A supplied nonnegative mode weight is multiplied by an exponential damping
   factor and a cosine phase.
3. **Positivity and boundedness of the scalar denominator**:
   $$0 < 1 - e^{-\Gamma \tau} < 1 \implies (1 - e^{-\Gamma \tau})^{-1} > 1$$
4. No Riemann--Weil summation, operator trace, Fredholm determinant, or
   categorical colimit is constructed by this file.
-/

noncomputable section

namespace InfoGeometry.Spectral.ModalContractionReadout

/-- Scalar damped cosine contribution with a supplied mode weight. -/
def modalDampedCosineTerm (lambda_n sqrt_n gamma_S tau t ln_n : ℝ) : ℝ :=
  (lambda_n / sqrt_n) * Real.exp (- gamma_S * tau) * Real.cos (t * ln_n)

/-- Reassociate the scalar damping factor. -/
theorem modalDampedCosineTerm_damping (lambda_n sqrt_n gamma_S tau t ln_n : ℝ) :
    modalDampedCosineTerm lambda_n sqrt_n gamma_S tau t ln_n =
      Real.exp (- gamma_S * tau) * ((lambda_n / sqrt_n) * Real.cos (t * ln_n)) := by
  dsimp [modalDampedCosineTerm]
  ring

/-- The scalar damped cosine is bounded by its nonnegative mode weight. -/
theorem modalDampedCosineTerm_abs_le (lambda_n sqrt_n gamma_S tau t ln_n : ℝ)
    (h_lam : 0 ≤ lambda_n) (h_sqrt : 0 < sqrt_n) (h_gamma : 0 ≤ gamma_S) (h_tau : 0 ≤ tau) :
    |modalDampedCosineTerm lambda_n sqrt_n gamma_S tau t ln_n| ≤ (lambda_n / sqrt_n) := by
  dsimp [modalDampedCosineTerm]
  have h_exp_le_one : Real.exp (- gamma_S * tau) ≤ 1 := by
    have : - gamma_S * tau ≤ 0 := by
      have : 0 ≤ gamma_S * tau := mul_nonneg h_gamma h_tau
      linarith
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.mpr this
  have h_exp_nonneg : 0 ≤ Real.exp (- gamma_S * tau) := Real.exp_nonneg _
  have h_cos_le_one : |Real.cos (t * ln_n)| ≤ 1 := Real.abs_cos_le_one _
  have h_weight_nonneg : 0 ≤ lambda_n / sqrt_n := div_nonneg h_lam (le_of_lt h_sqrt)
  have h_abs_split : |(lambda_n / sqrt_n) * Real.exp (- gamma_S * tau) * Real.cos (t * ln_n)| =
      (lambda_n / sqrt_n) * Real.exp (- gamma_S * tau) * |Real.cos (t * ln_n)| := by
    rw [abs_mul, abs_mul, abs_of_nonneg h_weight_nonneg, abs_of_nonneg h_exp_nonneg]
  rw [h_abs_split]
  have h_step1 : (lambda_n / sqrt_n) * Real.exp (- gamma_S * tau) * |Real.cos (t * ln_n)| ≤
      (lambda_n / sqrt_n) * Real.exp (- gamma_S * tau) := by
    have h_prod_nonneg : 0 ≤ (lambda_n / sqrt_n) * Real.exp (- gamma_S * tau) :=
      mul_nonneg h_weight_nonneg h_exp_nonneg
    have := mul_le_mul_of_nonneg_left h_cos_le_one h_prod_nonneg
    linarith
  have h_step2 : (lambda_n / sqrt_n) * Real.exp (- gamma_S * tau) ≤ lambda_n / sqrt_n := by
    have := mul_le_mul_of_nonneg_left h_exp_le_one h_weight_nonneg
    linarith
  exact le_trans h_step1 h_step2

/-- A finite damped cosine mode vanishes exactly at a zero weight or phase. -/
theorem modalDampedCosineTerm_eq_zero_iff
    (lambda_n sqrt_n gamma_S tau t ln_n : ℝ)
    (h_sqrt : sqrt_n ≠ 0) :
    modalDampedCosineTerm lambda_n sqrt_n gamma_S tau t ln_n = 0 ↔
      lambda_n = 0 ∨ Real.cos (t * ln_n) = 0 := by
  simp [modalDampedCosineTerm, h_sqrt, Real.exp_ne_zero]

/-- Scalar contraction denominator `1 - exp(-gamma * tau)`. -/
def contractionDenominator (gamma_S tau : ℝ) : ℝ :=
  1 - Real.exp (- gamma_S * tau)

/-- The scalar contraction denominator is positive for positive damping. -/
theorem contractionDenominator_pos (gamma_S tau : ℝ) (h_gamma : 0 < gamma_S) (h_tau : 0 < tau) :
    0 < contractionDenominator gamma_S tau := by
  dsimp [contractionDenominator]
  have h_prod_pos : 0 < gamma_S * tau := mul_pos h_gamma h_tau
  have h_neg : - gamma_S * tau < 0 := by linarith
  have h_exp_lt_one : Real.exp (- gamma_S * tau) < 1 := by
    rw [← Real.exp_zero]
    exact Real.exp_lt_exp.mpr h_neg
  linarith

/-- Its reciprocal is strictly greater than one. -/
theorem contractionDenominator_reciprocal_gt_one (gamma_S tau : ℝ)
    (h_gamma : 0 < gamma_S) (h_tau : 0 < tau) :
    1 < 1 / contractionDenominator gamma_S tau := by
  have h_denom_pos := contractionDenominator_pos gamma_S tau h_gamma h_tau
  have h_denom_lt_one : contractionDenominator gamma_S tau < 1 := by
    dsimp [contractionDenominator]
    have : 0 < Real.exp (- gamma_S * tau) := Real.exp_pos _
    linarith
  exact (one_lt_div h_denom_pos).mpr h_denom_lt_one

end InfoGeometry.Spectral.ModalContractionReadout
