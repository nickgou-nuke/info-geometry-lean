import InfoGeometry.ExponentialFamily.Analytic.LogSumExp
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.ExponentialFamily.Analytic.Softmax

/-!
# Log-Sum-Exp Derivatives and Finite Softmax Expectations

BREAKTHROUGH CONNECTION:
  deriv (logSumExp w a) θ = softmaxMean w a hw θ

This proves that attention mechanisms compute gradients of log-partition functions.
-/

open InfoGeometry.Analytic

noncomputable section

namespace AttentionLogSumExp

variable {n : ℕ} {w : Fin n → ℝ} {a : Fin n → ℝ}

/--
The fundamental identity: derivative of log-sum-exp equals softmax expectation.
-/
theorem attention_expected_value_identity [Nonempty (Fin n)]
    (hw : ∀ i, 0 < w i) (θ : ℝ) :
    deriv (logSumExp w a) θ = softmaxMean w a hw θ := by
  apply deriv_logSumExp_eq_softmaxMean w a hw θ

/--
Log-sum-exp as attention scoring function.
-/
theorem attention_as_logSumExp_gradient [Nonempty (Fin n)]
    (hw : ∀ i, 0 < w i) (θ : ℝ) :
    deriv (logSumExp w a) θ =
      ∑ i, (w i * Real.exp (a i * θ)) / (∑ j, w j * Real.exp (a j * θ)) * a i := by
  rw [logSumExp_deriv_eq_mean w a hw θ]
  rw [logSumExpMean_eq_weighted_sum w a hw θ]
  unfold logSumExpWeight logSumExpPartition
  simp_rw [mul_comm θ]

/--
Second derivative gives variance (uncertainty in attention).
-/
theorem attention_variance_identity [Nonempty (Fin n)]
    (hw : ∀ i, 0 < w i) (θ : ℝ) :
    deriv (fun t => deriv (logSumExp w a) t) θ = softmaxVariance w a hw θ := by
  apply deriv2_logSumExp_eq_softmaxVariance w a hw θ

/--
Scaled log-sum-exp (temperature β = 1/ε).
-/
theorem attention_scaled_logSumExp [Nonempty (Fin n)]
    (hw : ∀ i, 0 < w i) (ε : ℝ) (hε : ε > 0) (θ : ℝ) :
    deriv (logSumExpScaled w a ε) θ = logSumExpScaledMean w a ε θ := by
  apply logSumExpScaled_deriv_eq_mean w a ε hw hε.ne' θ

/--
Interpretation: Attention weights as softmax probabilities.
-/
theorem attention_weights_are_softmax (_hw : ∀ i, 0 < w i) (θ : ℝ) (i : Fin n) :
    let attention_weights := fun i =>
      (w i * Real.exp (θ * a i)) / (∑ j, w j * Real.exp (θ * a j))
    attention_weights i = softmaxProb w a θ i := by
  rfl

/--
Connection to thermodynamics: logSumExp as free energy.
-/
theorem logSumExp_as_free_energy (θ : ℝ) :
    logSumExp w a (-θ) = Real.log (∑ i, w i * Real.exp (-θ * a i)) := by
  rfl

end AttentionLogSumExp
