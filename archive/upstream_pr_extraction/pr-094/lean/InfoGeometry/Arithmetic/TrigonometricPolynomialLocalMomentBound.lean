import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

noncomputable section

open scoped BigOperators

namespace InfoGeometry.Arithmetic.TrigonometricPolynomialLocalMomentBound

/-- A finite complex trigonometric polynomial with frequencies `0, ..., N`. -/
def finiteTrigonometricPolynomial
    (N : ℕ) (a : ℕ → ℂ) (t : ℝ) : ℂ :=
  ∑ n ∈ Finset.range (N + 1),
    a n * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (t : ℂ))

def derivativeBound (N : ℕ) : NNReal :=
  ⟨∑ n ∈ Finset.range (N + 1), 2 * Real.pi * (n : ℝ), by positivity⟩

/-- Derivative of a finite trigonometric polynomial, term by term. -/
theorem hasDerivAt_finiteTrigonometricPolynomial
    (N : ℕ) (a : ℕ → ℂ) (t : ℝ) :
    HasDerivAt (finiteTrigonometricPolynomial N a)
      (∑ n ∈ Finset.range (N + 1),
        a n *
          (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (t : ℂ)) *
            (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ)))) t := by
  classical
  unfold finiteTrigonometricPolynomial
  apply HasDerivAt.fun_sum
  intro n hn
  let C : ℂ := 2 * (Real.pi : ℂ) * Complex.I * (n : ℂ)
  have hlin : HasDerivAt (fun x : ℝ => C * (x : ℂ)) C t := by
    simpa [C] using
      (ContinuousLinearMap.hasDerivAt Complex.ofRealCLM (x := t)).const_mul C
  have hexp : HasDerivAt
      (fun x : ℝ => Complex.exp (C * (x : ℂ)))
      (Complex.exp (C * (t : ℂ)) * C) t := by
    simpa using (Complex.hasDerivAt_exp (C * (t : ℂ))).comp t hlin
  simpa [C, mul_assoc, mul_left_comm, mul_comm] using hexp.const_mul (a n)

theorem deriv_finiteTrigonometricPolynomial
    (N : ℕ) (a : ℕ → ℂ) (t : ℝ) :
    deriv (finiteTrigonometricPolynomial N a) t =
      ∑ n ∈ Finset.range (N + 1),
        a n *
          (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (t : ℂ)) *
            (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ))) :=
  (hasDerivAt_finiteTrigonometricPolynomial N a t).deriv

theorem norm_deriv_finiteTrigonometricPolynomial_le
    (N : ℕ) (a : ℕ → ℂ) (t : ℝ) :
    ‖deriv (finiteTrigonometricPolynomial N a) t‖ ≤
      ∑ n ∈ Finset.range (N + 1),
        ‖a n *
          (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (t : ℂ)) *
            (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ)))‖ := by
  rw [deriv_finiteTrigonometricPolynomial]
  exact norm_sum_le _ _

/- The oscillatory exponential has unit norm, so the derivative estimate can
be written directly in terms of the coefficient norms and frequencies. -/
theorem norm_deriv_finiteTrigonometricPolynomial_le_weighted
    (N : ℕ) (a : ℕ → ℂ) (t : ℝ) :
    ‖deriv (finiteTrigonometricPolynomial N a) t‖ ≤
      ∑ n ∈ Finset.range (N + 1),
        ‖a n‖ * ‖2 * (Real.pi : ℂ) * Complex.I * (n : ℂ)‖ := by
  rw [deriv_finiteTrigonometricPolynomial]
  refine le_trans (norm_sum_le _ _) ?_
  apply Finset.sum_le_sum
  intro n hn
  let z : ℂ := 2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (t : ℂ)
  have hz : z.re = 0 := by
    dsimp [z]
    norm_num [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im]
  rw [norm_mul, norm_mul, Complex.norm_exp, hz, Real.exp_zero]
  simp

theorem norm_deriv_finiteTrigonometricPolynomial_le_of_coeff_norm_le_one
    (N : ℕ) (a : ℕ → ℂ) (t : ℝ)
    (ha : ∀ n ∈ Finset.range (N + 1), ‖a n‖ ≤ 1) :
    ‖deriv (finiteTrigonometricPolynomial N a) t‖ ≤
      ∑ n ∈ Finset.range (N + 1), 2 * Real.pi * (n : ℝ) := by
  rw [deriv_finiteTrigonometricPolynomial]
  refine le_trans (norm_sum_le _ _) ?_
  apply Finset.sum_le_sum
  intro n hn
  have hz : (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (t : ℂ)).re = 0 := by
    norm_num [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im]
  have hfreq : ‖2 * (Real.pi : ℂ) * Complex.I * (n : ℂ)‖ =
      2 * Real.pi * (n : ℝ) := by
    rw [norm_mul, norm_mul, norm_mul]
    simp [Real.norm_eq_abs, abs_of_nonneg Real.pi_pos.le]
  calc
    ‖a n * (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (t : ℂ)) *
        (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ)))‖ =
        ‖a n‖ * (‖Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (t : ℂ))‖ *
          ‖2 * (Real.pi : ℂ) * Complex.I * (n : ℂ)‖) := by rw [norm_mul, norm_mul]
    _ = ‖a n‖ * (2 * Real.pi * (n : ℝ)) := by
      rw [Complex.norm_exp, hz, Real.exp_zero, one_mul, hfreq]
    _ ≤ 2 * Real.pi * (n : ℝ) := by
      have hn0 : 0 ≤ (n : ℝ) := by positivity
      have hnonneg : 0 ≤ (2 : ℝ) * Real.pi * (n : ℝ) :=
        mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) Real.pi_pos.le) hn0
      simpa using mul_le_mul_of_nonneg_right (ha n hn) hnonneg

theorem finiteTrigonometricPolynomial_lipschitz_of_coeff_norm_le_one
    (N : ℕ) (a : ℕ → ℂ)
    (ha : ∀ n ∈ Finset.range (N + 1), ‖a n‖ ≤ 1) :
    LipschitzWith (derivativeBound N) (finiteTrigonometricPolynomial N a) := by
  apply lipschitzWith_of_nnnorm_deriv_le
  · exact fun t => (hasDerivAt_finiteTrigonometricPolynomial N a t).differentiableAt
  · intro t
    apply NNReal.coe_le_coe.1
    change ‖deriv (finiteTrigonometricPolynomial N a) t‖ ≤
      ∑ n ∈ Finset.range (N + 1), 2 * Real.pi * (n : ℝ)
    exact norm_deriv_finiteTrigonometricPolynomial_le_of_coeff_norm_le_one N a t ha

theorem finiteTrigonometricPolynomial_pointwise_persistence
    (N : ℕ) (a : ℕ → ℂ) (t : ℝ)
    (ha : ∀ n ∈ Finset.range (N + 1), ‖a n‖ ≤ 1) :
    ‖finiteTrigonometricPolynomial N a t - finiteTrigonometricPolynomial N a 0‖ ≤
      (derivativeBound N : ℝ) * |t| := by
  have h := finiteTrigonometricPolynomial_lipschitz_of_coeff_norm_le_one N a ha
    |>.norm_sub_le t 0
  simpa [Real.norm_eq_abs, abs_sub_comm] using h

theorem finiteTrigonometricPolynomial_norm_at_zero_sub_le_norm_at
    (N : ℕ) (a : ℕ → ℂ) (t : ℝ)
    (ha : ∀ n ∈ Finset.range (N + 1), ‖a n‖ ≤ 1) :
    ‖finiteTrigonometricPolynomial N a 0‖ -
        (derivativeBound N : ℝ) * |t| ≤
      ‖finiteTrigonometricPolynomial N a t‖ := by
  have hp := finiteTrigonometricPolynomial_pointwise_persistence N a t ha
  have htriangle := norm_sub_le
    (finiteTrigonometricPolynomial N a t)
    (finiteTrigonometricPolynomial N a t - finiteTrigonometricPolynomial N a 0)
  have hzero :
      ‖finiteTrigonometricPolynomial N a t - finiteTrigonometricPolynomial N a 0‖ ≤
        (derivativeBound N : ℝ) * |t| := hp
  have hsum :
      ‖finiteTrigonometricPolynomial N a 0‖ ≤
        ‖finiteTrigonometricPolynomial N a t‖ +
          ‖finiteTrigonometricPolynomial N a t - finiteTrigonometricPolynomial N a 0‖ := by
    simpa [sub_sub_cancel] using htriangle
  linarith

end InfoGeometry.Arithmetic.TrigonometricPolynomialLocalMomentBound
