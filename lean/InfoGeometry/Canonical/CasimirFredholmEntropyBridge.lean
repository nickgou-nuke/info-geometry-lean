import Mathlib.Data.Real.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic
import InfoGeometry.Canonical.UHFInductiveColimitBoundary
import InfoGeometry.Canonical.UHFWeilPositivityBridge
import InfoGeometry.Canonical.FredholmResolventDiscreteSpectrumBridge

/-!
# Casimir-Fredholm Entropy and Modular Dissipative Thermodynamics in the A_infinity Colimit

This module formalizes:
1. Casimir-dependent dissipation rates: $\lambda_n(w) = \lambda_0 + \kappa * C(w) > 0$.
2. Fredholm entropy of the dissipative flow:
   $$S_{\mathrm{Fredholm}, n}(\tau) = -\sum_{w} \log(1 - e^{-\tau \lambda_n(w)})$$
3. Strict nonnegativity of Fredholm entropy: $S_{\mathrm{Fredholm}, n}(\tau) \ge 0$.
4. Inductive normalized entropy density:
   $$s_n(\tau) = \frac{1}{2^n} S_{\mathrm{Fredholm}, n}(\tau) \implies s_{n+1}(\tau) = s_n(\tau)$$
5. The derivative of each summand is strictly negative for positive rate and time;
   each summand, the finite sum, and its normalization are strictly decreasing.
The results concern finite sums and successor compatibility, not an analytic
infinite-dimensional determinant.
-/

noncomputable section

open Real Complex
open scoped BigOperators

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace InfoGeometry.Canonical.CasimirFredholmEntropy

open InfoGeometry.Canonical.UHFInductiveColimitBoundary
open InfoGeometry.Canonical.UHFInductiveLimitBoundary
open InfoGeometry.Canonical.UHFWeilPositivity
open InfoGeometry.Canonical.FredholmResolvent

/-- Single bitword entropy term: -log(1 - exp(-tau * rate)). -/
def bitwordEntropy (rate : ℝ) (tau : ℝ) : ℝ :=
  - Real.log (1 - Real.exp (-tau * rate))

/-- 🏆 THEOREM 1: Single Bitword Entropy Nonnegativity for rate > 0 and tau > 0. -/
theorem bitwordEntropy_nonneg (rate : ℝ) (hrate : 0 < rate) (tau : ℝ) (htau : 0 < tau) :
    0 ≤ bitwordEntropy rate tau := by
  dsimp [bitwordEntropy]
  have h_prod : 0 < tau * rate := mul_pos htau hrate
  have h_exp_lt : Real.exp (-tau * rate) < 1 := by
    rw [← Real.exp_zero]
    exact Real.exp_lt_exp.mpr (by linarith)
  have h_exp_pos : 0 < Real.exp (-tau * rate) := Real.exp_pos (-tau * rate)
  have h_sub_pos : 0 < 1 - Real.exp (-tau * rate) := by linarith
  have h_sub_le : 1 - Real.exp (-tau * rate) ≤ 1 := by linarith
  have h_log_le : Real.log (1 - Real.exp (-tau * rate)) ≤ 0 := by
    rw [← Real.log_one]
    exact Real.log_le_log h_sub_pos h_sub_le
  linarith

/-- Derivative of the logarithmic summand on the positive time/rate domain. -/
theorem hasDerivAt_bitwordEntropy (rate tau : ℝ)
    (hrate : 0 < rate) (htau : 0 < tau) :
    HasDerivAt (bitwordEntropy rate)
      (-(rate * Real.exp (-tau * rate) / (1 - Real.exp (-tau * rate)))) tau := by
  have hden : 0 < 1 - Real.exp (-tau * rate) := by
    apply sub_pos.mpr
    rw [Real.exp_lt_one_iff]
    nlinarith
  have hexp : HasDerivAt (fun t : ℝ => Real.exp (-t * rate))
      (Real.exp (-tau * rate) * (-rate)) tau := by
    simpa using (((hasDerivAt_id tau).neg.mul_const rate).exp)
  convert ((hexp.const_sub 1).log (ne_of_gt hden)).neg using 1
  simp [bitwordEntropy]
  ring

theorem deriv_bitwordEntropy_neg (rate tau : ℝ)
    (hrate : 0 < rate) (htau : 0 < tau) :
    deriv (bitwordEntropy rate) tau < 0 := by
  rw [(hasDerivAt_bitwordEntropy rate tau hrate htau).deriv]
  apply neg_neg_of_pos
  apply div_pos (mul_pos hrate (Real.exp_pos _))
  apply sub_pos.mpr
  rw [Real.exp_lt_one_iff]
  nlinarith

/-- Strict decrease follows from the order properties of exponential and logarithm. -/
theorem bitwordEntropy_strictAntiOn (rate : ℝ) (hrate : 0 < rate) :
    StrictAntiOn (bitwordEntropy rate) (Set.Ioi 0) := by
  intro s hs t ht hst
  change -Real.log (1 - Real.exp (-t * rate)) <
    -Real.log (1 - Real.exp (-s * rate))
  apply neg_lt_neg
  apply Real.log_lt_log
  · apply sub_pos.mpr
    rw [Real.exp_lt_one_iff]
    have hs' : 0 < s := hs
    nlinarith
  · have hexp : Real.exp (-t * rate) < Real.exp (-s * rate) := by
      apply Real.exp_lt_exp.mpr
      nlinarith
    linarith

/-- Total finite logarithmic sum at stage `n`. -/
def stageFredholmEntropy (n : ℕ) (R : StageDissipationRates n) (tau : ℝ) : ℝ :=
  ∑ w : BitWord n, bitwordEntropy (R.rate w) tau

/-- Every nonempty finite stage is strictly decreasing on positive times. -/
theorem stageFredholmEntropy_strictAntiOn (n : ℕ) (R : StageDissipationRates n) :
    StrictAntiOn (stageFredholmEntropy n R) (Set.Ioi 0) := by
  intro s hs t ht hst
  apply Finset.sum_lt_sum
  · intro w _
    exact le_of_lt (bitwordEntropy_strictAntiOn (R.rate w) (R.rate_pos w) hs ht hst)
  · refine ⟨(fun _ => false), Finset.mem_univ _, ?_⟩
    exact bitwordEntropy_strictAntiOn _ (R.rate_pos _) hs ht hst

/-- Differentiation commutes with the actual finite stage sum. -/
theorem hasDerivAt_stageFredholmEntropy (n : ℕ) (R : StageDissipationRates n)
    (tau : ℝ) (htau : 0 < tau) :
    HasDerivAt (stageFredholmEntropy n R)
      (∑ w : BitWord n,
        -(R.rate w * Real.exp (-tau * R.rate w) /
          (1 - Real.exp (-tau * R.rate w)))) tau := by
  convert (HasDerivAt.sum (u := Finset.univ) (fun w _ =>
    hasDerivAt_bitwordEntropy (R.rate w) tau (R.rate_pos w) htau)) using 1
  ext t
  simp [stageFredholmEntropy]

/-- The derivative of the finite sum is nonpositive at positive times. -/
theorem deriv_stageFredholmEntropy_nonpos (n : ℕ) (R : StageDissipationRates n)
    (tau : ℝ) (htau : 0 < tau) :
    deriv (stageFredholmEntropy n R) tau ≤ 0 := by
  rw [(hasDerivAt_stageFredholmEntropy n R tau htau).deriv]
  apply Finset.sum_nonpos
  intro w _
  have h := deriv_bitwordEntropy_neg (R.rate w) tau (R.rate_pos w) htau
  rw [(hasDerivAt_bitwordEntropy (R.rate w) tau (R.rate_pos w) htau).deriv] at h
  exact le_of_lt h

/-- 🏆 THEOREM 2: Total Fredholm Entropy Nonnegativity. -/
theorem stageFredholmEntropy_nonneg (n : ℕ) (R : StageDissipationRates n) (tau : ℝ) (htau : 0 < tau) :
    0 ≤ stageFredholmEntropy n R tau := by
  dsimp [stageFredholmEntropy]
  apply Finset.sum_nonneg
  intro w hw
  exact bitwordEntropy_nonneg (R.rate w) (R.rate_pos w) tau htau

/-- Normalized stage entropy density: s_n(tau) = (1 / 2^n) * S_n(tau). -/
def stageEntropyDensity (n : ℕ) (R : StageDissipationRates n) (tau : ℝ) : ℝ :=
  (1 / (2 ^ n : ℝ)) * stageFredholmEntropy n R tau

/-- Positive normalization preserves strict decrease. -/
theorem stageEntropyDensity_strictAntiOn (n : ℕ) (R : StageDissipationRates n) :
    StrictAntiOn (stageEntropyDensity n R) (Set.Ioi 0) := by
  intro s hs t ht hst
  exact mul_lt_mul_of_pos_left
    (stageFredholmEntropy_strictAntiOn n R hs ht hst) (by positivity)

/-- 🏆 THEOREM 3: Stage Entropy Density Nonnegativity. -/
theorem stageEntropyDensity_nonneg (n : ℕ) (R : StageDissipationRates n) (tau : ℝ) (htau : 0 < tau) :
    0 ≤ stageEntropyDensity n R tau := by
  dsimp [stageEntropyDensity]
  have h_pos : 0 ≤ 1 / (2 ^ n : ℝ) := by positivity
  exact mul_nonneg h_pos (stageFredholmEntropy_nonneg n R tau htau)

/-- Complex representation of bitword entropy as a diagonal observable. -/
def entropyObservable (n : ℕ) (R : StageDissipationRates n) (tau : ℝ) : DiagAlg n :=
  fun w => (bitwordEntropy (R.rate w) tau : ℂ)

/-- 🏆 THEOREM 4: Colimit Tower Compatibility of Normalized Entropy Density. -/
theorem stageEntropyDensity_colimit_compat (n : ℕ) (R : StageDissipationRates n) (tau : ℝ) :
    stageEntropyDensity (n + 1) (embedRates n R) tau =
      stageEntropyDensity n R tau := by
  dsimp [stageEntropyDensity, stageFredholmEntropy]
  have h_trace_succ : (stageTrace (n + 1) (entropyObservable (n + 1) (embedRates n R) tau)).re =
                      (stageTrace n (entropyObservable n R tau)).re := by
    have h_diag : entropyObservable (n + 1) (embedRates n R) tau =
                  diagEmbedSucc n (entropyObservable n R tau) := by
      funext w
      dsimp [entropyObservable, embedRates, diagEmbedSucc]
    rw [h_diag, stageTrace_diagEmbedSucc]
  dsimp [stageTrace, entropyObservable] at h_trace_succ
  have h_c_div (k : ℕ) : (2 ^ k : ℂ)⁻¹ = ↑(1 / (2 ^ k : ℝ)) := by push_cast; simp
  rw [h_c_div (n + 1), h_c_div n] at h_trace_succ
  simp only [mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero] at h_trace_succ
  have h_re (k : ℕ) (R' : StageDissipationRates k) :
      (∑ w : BitWord k, ((bitwordEntropy (R'.rate w) tau : ℂ))).re =
      ∑ w : BitWord k, bitwordEntropy (R'.rate w) tau := by
    simp [Complex.re_sum]
  rwa [h_re (n + 1) (embedRates n R), h_re n R] at h_trace_succ

/-- 🏆 THEOREM 5: Master Casimir-Fredholm Entropy Synthesis Packet. -/
theorem master_casimir_fredholm_entropy_synthesis
    (n : ℕ) (R : StageDissipationRates n) (tau : ℝ) (htau : 0 < tau) :
    (0 ≤ stageFredholmEntropy n R tau) ∧
    (0 ≤ stageEntropyDensity n R tau) ∧
    (stageEntropyDensity (n + 1) (embedRates n R) tau = stageEntropyDensity n R tau) := by
  exact ⟨stageFredholmEntropy_nonneg n R tau htau,
         stageEntropyDensity_nonneg n R tau htau,
         stageEntropyDensity_colimit_compat n R tau⟩

end InfoGeometry.Canonical.CasimirFredholmEntropy
