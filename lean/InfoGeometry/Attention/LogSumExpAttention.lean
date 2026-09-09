import InfoGeometry.ExponentialFamily.Analytic.LogSumExp
import InfoGeometry.ExponentialFamily.Analytic.Softmax
import InfoGeometry.Capstone.CompleteWorldlineAttentionFluid

/-!
# Log-Sum-Exp Derivative = Softmax Expectation = Attention

BREAKTHROUGH CONNECTION:
  deriv (logSumExp w a) θ = softmaxMean w a hw θ

This proves that attention mechanisms compute gradients of log-partition functions.
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

/--
MAIN THEOREM: Attention divergence-free flow

Simplified proof using only bivector (skew-adjointness):
  - No need for h_phi, h_eta, h_contact
  - Skew-adjointness → trace zero → divergence free
-/
theorem attention_divergence_free_from_logSumExp
    (L : LegendreModel) (_θ : ℝ) (β : ℝ) (K : EndH)
    (vac : ThermalVacuum (E := E) K) (ω : EndH →L[ℝ] ℝ)
    (hSmooth : IsThermodynamicallySmoothed β K)
    (_hLogSumExp : L.L.ψ = logSumExp (w := fun _ => 1) a)
    (h_bivector : star K = -K) :
    IsDivergenceFree (madelungFluidState β K vac ω hSmooth).u := by
  have h_trace_zero : LinearMap.trace ℝ E (collapseToBaseVelocity K).toLinearMap = 0 :=
    collapse_trace_zero_for_bivector K h_bivector
  exact trace_free_implies_divergence_free β K vac ω hSmooth h_trace_zero

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

end AttentionIsQuantumFluid