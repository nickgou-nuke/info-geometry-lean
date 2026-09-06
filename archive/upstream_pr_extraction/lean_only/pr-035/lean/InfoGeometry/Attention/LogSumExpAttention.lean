import InfoGeometry.ExponentialFamily.Analytic.LogSumExp
import InfoGeometry.ExponentialFamily.Analytic.Softmax
import InfoGeometry.Capstone.CompleteWorldlineAttentionFluid

/-!
# Log-Sum-Exp Derivative = Softmax Expectation = Attention

The first theorem block records the finite exponential-family identities
underlying the attention readout.  The final theorem is kept as a separate
Madelung-fluid consequence of skew-adjointness; it does not depend on the
log-sum-exp hypotheses.
-/

open InfoGeometry.Analytic
open InfoGeometry.LogPotential
open InfoGeometry.Canonical
open InfoGeometry.Krein
open InfoGeometry.CompleteWorldline

noncomputable section

namespace AttentionIsQuantumFluid

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

variable {E : Type _}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable [FiniteDimensional ℝ E]

local notation "EndH" => AlgebraEnd E

/-- Skew-adjoint bivector generators have divergence-free Madelung velocity.

This is independent of the log-sum-exp/attention identities above: the proof
uses only the trace-zero consequence of `star K = -K`.
-/
theorem madelungFluid_divergenceFree_of_bivectorGenerator
    (β : ℝ) (K : EndH)
    (vac : ThermalVacuum (E := E) K) (ω : EndH →L[ℝ] ℝ)
    (hSmooth : IsThermodynamicallySmoothed β K)
    (h_bivector : star K = -K) :
    IsDivergenceFree (madelungFluidState β K vac ω hSmooth).u := by
  have h_trace_zero : LinearMap.trace ℝ E (collapseToBaseVelocity K).toLinearMap = 0 :=
    collapse_trace_zero_for_bivector K h_bivector
  exact trace_free_implies_divergence_free β K vac ω hSmooth h_trace_zero

/-- The locally defined attention weights are the softmax probabilities. -/
theorem attention_weights_eq_softmaxProb (_hw : ∀ i, 0 < w i) (θ : ℝ) (i : Fin n) :
    let attention_weights := fun i =>
      (w i * Real.exp (θ * a i)) / (∑ j, w j * Real.exp (θ * a j))
    attention_weights i = softmaxProb w a θ i := by
  rfl

/-- The finite log-sum-exp is definitionally the logarithm of its partition sum. -/
theorem logSumExp_eq_logPartition (θ : ℝ) :
    logSumExp w a (-θ) = Real.log (∑ i, w i * Real.exp (-θ * a i)) := by
  rfl

end AttentionIsQuantumFluid
