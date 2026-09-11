/-
Copyright (c) 2026 nickgou-nuke. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: nickgou-nuke contributors
-/
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic
import InfoGeometry.Physics.AitchisonTraceDeterminantBridge
import InfoGeometry.Physics.AitchisonCartanDuallyFlatBridge

open scoped BigOperators
open Real
open InfoGeometry.Physics.AitchisonTraceDeterminant
open InfoGeometry.Physics.AitchisonCartanDuallyFlat

set_option linter.unusedVariables false

noncomputable section

namespace InfoGeometry.Physics.AmariSurprisalSphereIwasawa

variable {D : ℕ}

/-! ## 1. Surprisal Vector and Additive Log-Ratio (alr) -/

/-- Surprisal (self-information) of state i: $s_i = -\ln p_i$. -/
def surprisal (P : PositiveDistribution D) (i : Fin D) : ℝ :=
  - Real.log (P.p i)

/-- 🏆 THEOREM 1: Shannon entropy is the expected surprisal: $H(P) = \sum_i p_i s_i$. -/
theorem entropy_eq_expected_surprisal (P : PositiveDistribution D) :
    shannonEntropy P = ∑ i, P.p i * surprisal P i := by
  unfold shannonEntropy dualPotential surprisal
  simp_rw [mul_neg]
  rw [← Finset.sum_neg_distrib]

/-- 🏆 THEOREM 2: The centered log-ratio is the negative centered surprisal:
    $\mathrm{clr}(P)_i = -s_i + \bar{s}$. -/
theorem clr_eq_neg_centered_surprisal (P : PositiveDistribution D) (hD : 0 < D) (i : Fin D) :
    clr P hD i = - surprisal P i + (1 / (D : ℝ)) * ∑ k, surprisal P k := by
  unfold clr logMean surprisal
  have h_sum_surp : (∑ k, - Real.log (P.p k)) = - ∑ k, Real.log (P.p k) := by
    rw [← Finset.sum_neg_distrib]
  rw [h_sum_surp, mul_neg, inv_eq_one_div]
  ring

/-- Additive log-ratio (alr) relative to reference pole d_ref:
    $\mathrm{alr}(P, d_{\mathrm{ref}})_i = s(d_{\mathrm{ref}}) - s(i) = \ln(p_i / p_{d_{\mathrm{ref}}})$. -/
def alr (P : PositiveDistribution D) (d_ref : Fin D) (i : Fin D) : ℝ :=
  surprisal P d_ref - surprisal P i

/-- 🏆 THEOREM 3: The alr coordinate is identically the log-ratio against the reference pole. -/
theorem alr_eq_log_ratio (P : PositiveDistribution D) (d_ref : Fin D) (i : Fin D) :
    alr P d_ref i = Real.log (P.p i / P.p d_ref) := by
  unfold alr surprisal
  have h_pos_i := P.h_pos i
  have h_pos_ref := P.h_pos d_ref
  rw [Real.log_div (ne_of_gt h_pos_i) (ne_of_gt h_pos_ref)]
  ring

/-- 🏆 THEOREM 4: Natural parameter exponential: $\exp(\theta^i) = p_i / p_{d_{\mathrm{ref}}}$. -/
theorem exp_alr_eq_ratio (P : PositiveDistribution D) (d_ref : Fin D) (i : Fin D) :
    Real.exp (alr P d_ref i) = P.p i / P.p d_ref := by
  rw [alr_eq_log_ratio]
  have h_ratio_pos : 0 < P.p i / P.p d_ref := div_pos (P.h_pos i) (P.h_pos d_ref)
  exact Real.exp_log h_ratio_pos

/-- 🏆 THEOREM 5: Free energy potential is identically the reference state surprisal:
    $\ln(\sum_i e^{\theta^i}) = s(d_{\mathrm{ref}})$. -/
theorem log_sum_exp_alr_eq_ref_surprisal (P : PositiveDistribution D) (d_ref : Fin D) :
    Real.log (∑ i, Real.exp (alr P d_ref i)) = surprisal P d_ref := by
  have h_term : ∀ i : Fin D, Real.exp (alr P d_ref i) = P.p i / P.p d_ref :=
    fun i => exp_alr_eq_ratio P d_ref i
  simp_rw [h_term, ← Finset.sum_div]
  rw [P.h_sum]
  unfold surprisal
  have h_pos_ref := P.h_pos d_ref
  rw [Real.log_div one_ne_zero (ne_of_gt h_pos_ref), Real.log_one, zero_sub]

/-! ## 2. The Square-Root Amplitude Map to the Sphere -/

/-- Bhattacharyya-Wootters square-root amplitude: $\xi_i = \sqrt{p_i}$. -/
def amplitude (P : PositiveDistribution D) (i : Fin D) : ℝ :=
  Real.sqrt (P.p i)

/-- Strict positivity of the probability amplitudes. -/
theorem amplitude_pos (P : PositiveDistribution D) (i : Fin D) :
    0 < amplitude P i :=
  Real.sqrt_pos.mpr (P.h_pos i)

/-- 🏆 THEOREM 6: Spinorization identity: $\xi_i^2 = p_i$. -/
theorem amplitude_sq_eq_prob (P : PositiveDistribution D) (i : Fin D) :
    (amplitude P i) ^ 2 = P.p i := by
  unfold amplitude
  exact Real.sq_sqrt (le_of_lt (P.h_pos i))

/-- 🏆 THEOREM 7: The amplitude vector lies on the unit sphere $S^{D-1}$: $\sum_i \xi_i^2 = 1$. -/
theorem sum_amplitude_sq_one (P : PositiveDistribution D) :
    ∑ i, (amplitude P i) ^ 2 = 1 := by
  have h_sq : ∀ i : Fin D, (amplitude P i) ^ 2 = P.p i :=
    fun i => amplitude_sq_eq_prob P i
  simp_rw [h_sq]
  exact P.h_sum

/-- Bhattacharyya spherical inner product between two states. -/
def bhattacharyyaInner (P Q : PositiveDistribution D) : ℝ :=
  ∑ i, amplitude P i * amplitude Q i

/-- 🏆 THEOREM 8: Self-overlap on the sphere is normalized to 1: $\langle \xi_P, \xi_P \rangle = 1$. -/
theorem bhattacharyyaInner_self (P : PositiveDistribution D) :
    bhattacharyyaInner P P = 1 := by
  unfold bhattacharyyaInner
  have h_sq : ∀ i : Fin D, amplitude P i * amplitude P i = (amplitude P i) ^ 2 := by
    intro i; ring
  simp_rw [h_sq]
  exact sum_amplitude_sq_one P

/-- 🏆 THEOREM 9: Symmetry of the spherical inner product. -/
theorem bhattacharyyaInner_symm (P Q : PositiveDistribution D) :
    bhattacharyyaInner P Q = bhattacharyyaInner Q P := by
  unfold bhattacharyyaInner
  have h_comm : ∀ i : Fin D, amplitude P i * amplitude Q i = amplitude Q i * amplitude P i := by
    intro i; ring
  simp_rw [h_comm]

/-- 🏆 THEOREM 10: Strict positivity of the spherical inner product. -/
theorem bhattacharyyaInner_pos (P Q : PositiveDistribution D) (hD : 0 < D) :
    0 < bhattacharyyaInner P Q := by
  unfold bhattacharyyaInner
  have h_elem : (⟨0, hD⟩ : Fin D) ∈ Finset.univ := Finset.mem_univ _
  have h_pos_zero : 0 < amplitude P ⟨0, hD⟩ * amplitude Q ⟨0, hD⟩ :=
    mul_pos (amplitude_pos P ⟨0, hD⟩) (amplitude_pos Q ⟨0, hD⟩)
  exact Finset.sum_pos' (fun i _ => le_of_lt (mul_pos (amplitude_pos P i) (amplitude_pos Q i)))
    ⟨⟨0, hD⟩, h_elem, h_pos_zero⟩

/-! ## 3. Amari Curvature Contraction & Inönü-Wigner Factor -/

/-- The Amari sectional curvature factor: $K(\alpha) = \frac{1 - \alpha^2}{4}$. -/
def curvatureFactor (alpha : ℝ) : ℝ :=
  (1 - alpha ^ 2) / 4

/-- 🏆 THEOREM 11: At $\alpha = 0$ (Fisher-Rao Levi-Civita connection on the sphere),
    the curvature is $+1/4$. -/
theorem curvatureFactor_zero : curvatureFactor 0 = 1 / 4 := by
  unfold curvatureFactor
  ring

/-- 🏆 THEOREM 12: At $\alpha = +1$ (Exponential connection $\nabla^{(1)}$, e-flat),
    the curvature vanishes identically: $R^{(1)} = 0$. -/
theorem curvatureFactor_one : curvatureFactor 1 = 0 := by
  unfold curvatureFactor
  ring

/-- 🏆 THEOREM 13: At $\alpha = -1$ (Mixture connection $\nabla^{(-1)}$, m-flat),
    the curvature vanishes identically: $R^{(-1)} = 0$. -/
theorem curvatureFactor_neg_one : curvatureFactor (-1) = 0 := by
  unfold curvatureFactor
  ring

/-- 🏆 THEOREM 14: Parity reflection symmetry of the curvature contraction factor:
    $K(-\alpha) = K(\alpha)$. -/
theorem curvatureFactor_symm (alpha : ℝ) :
    curvatureFactor (-alpha) = curvatureFactor alpha := by
  unfold curvatureFactor
  have : (-alpha) ^ 2 = alpha ^ 2 := neg_sq alpha
  rw [this]

/-- 🏆 THEOREM 15: The Fisher-Rao sphere achieves maximal curvature: $K(\alpha) \le 1/4$ for all $\alpha$. -/
theorem curvatureFactor_le_quarter (alpha : ℝ) :
    curvatureFactor alpha ≤ 1 / 4 := by
  unfold curvatureFactor
  have h_sq_nonneg : 0 ≤ alpha ^ 2 := sq_nonneg alpha
  have : 1 - alpha ^ 2 ≤ 1 := by linarith
  linarith

/-! ## 4. Master Conjunction -/

/-- Certified structural synthesis of the Amari Surprisal Sphere Iwasawa Bridge. -/
structure CertifiedAmariSurprisalSphereIwasawaSynthesis : Prop where
  h_entropy_expected_surprisal : ∀ (P : PositiveDistribution D),
    shannonEntropy P = ∑ i, P.p i * surprisal P i
  h_clr_surprisal : ∀ (P : PositiveDistribution D) (hD : 0 < D) (i : Fin D),
    clr P hD i = - surprisal P i + (1 / (D : ℝ)) * ∑ k, surprisal P k
  h_alr_log_ratio : ∀ (P : PositiveDistribution D) (d_ref : Fin D) (i : Fin D),
    alr P d_ref i = Real.log (P.p i / P.p d_ref)
  h_log_sum_exp_surprisal : ∀ (P : PositiveDistribution D) (d_ref : Fin D),
    Real.log (∑ i, Real.exp (alr P d_ref i)) = surprisal P d_ref
  h_amplitude_sq : ∀ (P : PositiveDistribution D) (i : Fin D),
    (amplitude P i) ^ 2 = P.p i
  h_sphere_normalization : ∀ (P : PositiveDistribution D),
    ∑ i, (amplitude P i) ^ 2 = 1
  h_inner_self : ∀ (P : PositiveDistribution D),
    bhattacharyyaInner P P = 1
  h_inner_symm : ∀ (P Q : PositiveDistribution D),
    bhattacharyyaInner P Q = bhattacharyyaInner Q P
  h_inner_pos : ∀ (P Q : PositiveDistribution D) (hD : 0 < D),
    0 < bhattacharyyaInner P Q
  h_curv_zero : curvatureFactor 0 = 1 / 4
  h_curv_one : curvatureFactor 1 = 0
  h_curv_neg_one : curvatureFactor (-1) = 0
  h_curv_symm : ∀ (alpha : ℝ), curvatureFactor (-alpha) = curvatureFactor alpha
  h_curv_bound : ∀ (alpha : ℝ), curvatureFactor alpha ≤ 1 / 4

/-- 🏆 MASTER CONJUNCTION: Certified Amari Surprisal Sphere Iwasawa Synthesis. -/
theorem certified_amari_surprisal_sphere_iwasawa_synthesis :
    CertifiedAmariSurprisalSphereIwasawaSynthesis (D := D) :=
  ⟨entropy_eq_expected_surprisal,
   clr_eq_neg_centered_surprisal,
   alr_eq_log_ratio,
   log_sum_exp_alr_eq_ref_surprisal,
   amplitude_sq_eq_prob,
   sum_amplitude_sq_one,
   bhattacharyyaInner_self,
   bhattacharyyaInner_symm,
   bhattacharyyaInner_pos,
   curvatureFactor_zero,
   curvatureFactor_one,
   curvatureFactor_neg_one,
   curvatureFactor_symm,
   curvatureFactor_le_quarter⟩

end InfoGeometry.Physics.AmariSurprisalSphereIwasawa
