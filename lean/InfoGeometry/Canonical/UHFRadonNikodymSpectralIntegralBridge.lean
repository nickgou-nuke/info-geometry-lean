import Mathlib.Data.Real.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic
import InfoGeometry.Canonical.UHFInductiveColimitBoundary
import InfoGeometry.Canonical.UHFWeilPositivityBridge

/-!
# Positive weighted finite traces and successor compatibility

This module formalizes:
1. The Radon-Nikodym spectral weight operator on UHF stage algebras:
   $$\Delta_{\mathrm{RN}, n}(f)(w) = e^{-\alpha_{\mathrm{RN}}(w)} f(w)$$
2. The Stage Radon-Nikodym Spectral Integral:
   $$I_n(f) = \tau_n(\Delta_{\mathrm{RN}, n}(f^* f))$$
3. Compatibility across the direct inductive colimit tower:
   $$I_{n+1}(\iota_n(f)) = I_n(f)$$
4. Reduction to the unweighted trace when every weight equals one:
   $$\left. \alpha_{\mathrm{RN}}(w) \right|_{\text{critical}} = 0 \implies I_n(f) = \tau_n(f^* f)$$

The carrier here is a finite family of strictly positive real weights. No
cohomology group, critical-line identification, or Radon–Nikodym theorem is
constructed by these declarations.
-/

noncomputable section

open Complex
open scoped BigOperators

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace InfoGeometry.Canonical.UHFRadonNikodymAnomaly

open InfoGeometry.Canonical.UHFInductiveColimitBoundary
open InfoGeometry.Canonical.UHFInductiveLimitBoundary
open InfoGeometry.Canonical.UHFWeilPositivity

/-- Discrete Radon-Nikodym weight factor on BitWord n. -/
structure StageCocycleWeight (n : ℕ) where
  weight : BitWord n → ℝ
  weight_pos : ∀ w, 0 < weight w

/-- Weighted integrand: w ↦ (weight w : ℂ) * star (f w) * f w. -/
def weightedIntegrand (n : ℕ) (W : StageCocycleWeight n) (f : DiagAlg n) : DiagAlg n :=
  fun w => (W.weight w : ℂ) * star (f w) * f w

/-- Spectral integral with respect to a StageCocycleWeight. -/
def stageSpectralIntegral (n : ℕ) (W : StageCocycleWeight n) (f : DiagAlg n) : ℝ :=
  (stageTrace n (weightedIntegrand n W f)).re

/-- The constant weight one. -/
def trivialWeight (n : ℕ) : StageCocycleWeight n where
  weight := fun _ => 1
  weight_pos := fun _ => by norm_num

/-- 🏆 THEOREM 1: The Trivial Cocycle Spectral Integral Matches the Standard Trace. -/
theorem stageSpectralIntegral_trivial_eq_trace (n : ℕ) (f : DiagAlg n) :
    stageSpectralIntegral n (trivialWeight n) f =
      (stageTrace n (diagMul n (diagStar n f) f)).re := by
  dsimp [stageSpectralIntegral]
  have h_int : weightedIntegrand n (trivialWeight n) f = diagMul n (diagStar n f) f := by
    funext w
    dsimp [weightedIntegrand, trivialWeight, diagMul, diagStar]
    simp only [ofReal_one, one_mul]
  rw [h_int]

/-- 🏆 THEOREM 2: Positivity of the Radon-Nikodym Spectral Integral. -/
theorem stageSpectralIntegral_nonneg (n : ℕ) (W : StageCocycleWeight n) (f : DiagAlg n) :
    0 ≤ stageSpectralIntegral n W f := by
  dsimp [stageSpectralIntegral, stageTrace, weightedIntegrand]
  have h_c_div : (2 ^ n : ℂ)⁻¹ = ↑(1 / (2 ^ n : ℝ)) := by push_cast; simp
  rw [h_c_div]
  simp only [mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero]
  have h_sum_re : (∑ w : BitWord n, ((W.weight w : ℂ) * (starRingEnd ℂ) (f w) * f w)).re =
                  ∑ w : BitWord n, (W.weight w * normSq (f w)) := by
    rw [Complex.re_sum]
    congr 1 with w
    have : ((W.weight w : ℂ) * (starRingEnd ℂ) (f w) * f w) = ↑(W.weight w) * ((starRingEnd ℂ) (f w) * f w) := by ring
    rw [this]
    simp only [mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero]
    exact congrArg (HMul.hMul (W.weight w)) (star_mul_self_re_eq_normSq (f w))
  rw [h_sum_re]
  have h_sum_nonneg : 0 ≤ ∑ w : BitWord n, (W.weight w * normSq (f w)) := by
    apply Finset.sum_nonneg
    intro w hw
    have hw_pos : 0 ≤ W.weight w := le_of_lt (W.weight_pos w)
    exact mul_nonneg hw_pos (normSq_nonneg (f w))
  have h_factor : 0 ≤ 1 / (2 ^ n : ℝ) := by positivity
  exact mul_nonneg h_factor h_sum_nonneg

/-- Pullback / Embedding of a StageCocycleWeight to the next level (n + 1). -/
def embedWeight (n : ℕ) (W : StageCocycleWeight n) : StageCocycleWeight (n + 1) where
  weight := fun w => W.weight (prefixSucc n w)
  weight_pos := fun w => W.weight_pos (prefixSucc n w)

/-- 🏆 THEOREM 3: Colimit Tower Compatibility of the Radon-Nikodym Spectral Integral. -/
theorem stageSpectralIntegral_colimit_compat (n : ℕ) (W : StageCocycleWeight n) (f : DiagAlg n) :
    stageSpectralIntegral (n + 1) (embedWeight n W) (diagEmbedSucc n f) =
      stageSpectralIntegral n W f := by
  dsimp [stageSpectralIntegral]
  have h_diag : weightedIntegrand (n + 1) (embedWeight n W) (diagEmbedSucc n f) =
                diagEmbedSucc n (weightedIntegrand n W f) := by
    funext w
    dsimp [weightedIntegrand, embedWeight, diagEmbedSucc]
  rw [h_diag]
  rw [stageTrace_diagEmbedSucc n (weightedIntegrand n W f)]

/-- Successor compatibility specialized to the constant weight one.
The historical name does not assert vanishing of a cohomology group. -/
theorem absence_of_cohomological_anomaly (n : ℕ) (f : DiagAlg n) :
    stageSpectralIntegral (n + 1) (embedWeight n (trivialWeight n)) (diagEmbedSucc n f) =
      (stageTrace n (diagMul n (diagStar n f) f)).re := by
  rw [stageSpectralIntegral_colimit_compat]
  exact stageSpectralIntegral_trivial_eq_trace n f

/-- 🏆 THEOREM 5: Master UHF Radon-Nikodym Spectral Integral Synthesis Packet. -/
theorem master_uhf_rn_anomaly_free_synthesis (n : ℕ) (W : StageCocycleWeight n) (f : DiagAlg n) :
    (0 ≤ stageSpectralIntegral n W f) ∧
    (stageSpectralIntegral (n + 1) (embedWeight n W) (diagEmbedSucc n f) = stageSpectralIntegral n W f) ∧
    (stageSpectralIntegral (n + 1) (embedWeight n (trivialWeight n)) (diagEmbedSucc n f) =
       (stageTrace n (diagMul n (diagStar n f) f)).re) := by
  exact ⟨stageSpectralIntegral_nonneg n W f,
         stageSpectralIntegral_colimit_compat n W f,
         absence_of_cohomological_anomaly n f⟩

end InfoGeometry.Canonical.UHFRadonNikodymAnomaly
