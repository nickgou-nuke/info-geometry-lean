/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.ExponentialFamily.Analytic.LogSumExp
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.ExponentialFamily.Analytic.Softmax
import InfoGeometry.Thermodynamics.SoftmaxGibbsVariationalPrinciple

/-!
# Log-Sum-Exp Derivatives and Finite Softmax Expectations

BREAKTHROUGH CONNECTION:
  deriv (logSumExp w a) θ = softmaxMean w a hw θ

This proves that attention mechanisms compute gradients of log-partition functions.
-/

open InfoGeometry.Analytic
open InfoGeometry.Thermodynamics.SoftmaxGibbsVariational

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

/-! The following statements record probability and free-energy properties of
the concrete finite attention weights. They replace definitional restatements
of `softmaxProb` and `logSumExp`. -/

/-- The explicit attention weights form a strictly positive probability
distribution. Positivity of the base weights and a nonempty finite index type
ensure the partition denominator is positive. -/
theorem attention_weights_are_strict_probability [Nonempty (Fin n)]
    (hw : ∀ i, 0 < w i) (θ : ℝ) :
    let attentionWeights : Fin n → ℝ := fun i =>
      (w i * Real.exp (θ * a i)) / (∑ j, w j * Real.exp (θ * a j))
    (∀ i, 0 < attentionWeights i) ∧ ∑ i, attentionWeights i = 1 := by
  refine ⟨?_, ?_⟩
  · intro i
    change 0 < softmaxProb w a θ i
    exact softmaxProb_pos (w := w) (a := a) hw θ i
  · change (∑ i, softmaxProb w a θ i) = 1
    exact softmaxProb_sum_one (w := w) (a := a) hw θ

/-- At unit base weights, the log-partition potential is the negative
equilibrium free energy for the Hamiltonian `Hᵢ = -aᵢ`. This identifies the
finite log-sum-exp with a thermodynamic potential through the Gibbs variational
owner, rather than merely unfolding its definition. -/
theorem logSumExp_eq_negative_gibbs_equilibrium_freeEnergy
    [Nonempty (Fin n)] (T : InverseTemperature) (a : Fin n → ℝ) :
    logSumExp (fun _ : Fin n => (1 : ℝ)) a T.beta =
      -T.beta * freeEnergy T (fun i => -a i)
        (gibbsState T (fun i => -a i)) := by
  rw [freeEnergy_gibbsState]
  have hpartition :
      partitionSum T (fun i : Fin n => -a i) =
        logSumExpPartition (fun _ : Fin n => (1 : ℝ)) a T.beta := by
    unfold partitionSum logSumExpPartition
    apply Finset.sum_congr rfl
    intro i hi
    rw [neg_mul_neg, one_mul]
  rw [hpartition]
  unfold logSumExp
  have hscale : -T.beta * (-(1 / T.beta)) = 1 := by
    field_simp [T.beta_ne_zero]
  rw [← mul_assoc, hscale, one_mul]

theorem attention_weights_are_softmax (θ : ℝ) (i : Fin n) :
    let attention_weights := fun i =>
      (w i * Real.exp (θ * a i)) / (∑ j, w j * Real.exp (θ * a j))
    attention_weights i = softmaxProb w a θ i := by
  rfl

theorem logSumExp_as_free_energy (θ : ℝ) :
    logSumExp w a (-θ) = Real.log (∑ i, w i * Real.exp (-θ * a i)) := by
  rfl

end AttentionLogSumExp
