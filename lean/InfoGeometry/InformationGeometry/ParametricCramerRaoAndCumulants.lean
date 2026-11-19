/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Analytic.LogSumExp
import InfoGeometry.ExponentialFamily.KLBregman
import InfoGeometry.ExponentialFamily.Legendre
import InfoGeometry.Information.MultiLogPotential
import InfoGeometry.Epistemology.ChentsovMetricInvariance
import InfoGeometry.InformationGeometry.ArakiDonaldVariational
import InfoGeometry.Canonical.CramerRaoUncertainty
import Mathlib.Analysis.Convex.Deriv

/-!
# Parametric Statistical Models, Genuine Cramér–Rao Inequality, and Unconditional Cumulants

This module grounds the classical information-geometry lane in explicit finite-sample
calculus and Mathlib analysis rather than assumed algebraic bounds:

1. **Score & Parametric Model Fisher Information**:
   - Defines `score`, `statMeanOf`, `statVariance`, and `modelFisherInfo`.
   - Proves `hasDerivAt_log_prob_eq_score` from positivity and pointwise differentiability,
     `deriv_prob_sum_eq_zero` and `expectation_score_eq_zero` from normalization `∑ x, p t x = 1`,
     `modelFisherInfo_eq_chentsov_fisherMetric`, and the covariance-derivative identity
     `hasDerivAt_expectation_eq_covariance_score`.
2. **Weighted Cauchy–Schwarz & Genuine Cramér–Rao Inequality**:
   - Proves `weighted_cauchy_schwarz` and exact equality characterization
     `weighted_cauchy_schwarz_eq_iff` via explicit non-negative quadratic residuals.
   - Derives `cramer_rao_covariance_bound`, `cramer_rao_hasDerivAt_bound`,
     `cramer_rao_unbiased_lower_bound`, exact affine-score saturation
     `cramer_rao_saturated_iff_affine_score`, and concrete instantiation into
     `CramerRaoUncertainty.heisenberg_from_cramer_rao`.
3. **Unconditional 1D Exponential-Family Cumulants & Strict Convexity**:
   - Bridges `ExponentialFamily.FiniteExponentialFamilyData` directly to `Analytic.logSumExp`,
     unconditionally discharging `hmean` in `KLParam_eq_LogPotential_bregman_of_statMean_eq_deriv`
     (`KLParam_eq_bregman_unconditional`) and proving second-cumulant Fisher variance and
     sufficient-statistic Cramér–Rao saturation.
   - Proves `logSumExpVariance_pos_of_nonconstant` and unconditional
     `logSumExp_strictConvexOn_of_nonconstant` via `strictConvexOn_univ_of_deriv2_pos`,
     constructing `logSumExpLegendre_of_nonconstant : LegendrePotential` with no external
     strict-convexity assumption.
4. **Multivariate `Information.FiniteExpFamily` Directional Cumulants & Pythagorean Law**:
   - Connects directional slices `t ↦ logPartition F (θ + t • v)` to `Analytic.logSumExp`,
     proving first/second directional cumulants (matching `statMean` and `fisherQuadratic`),
     multivariate `multiKL` non-negativity, three-point identity, and mixed-geodesic
     Pythagorean decomposition.
-/

noncomputable section

namespace InfoGeometry.InformationGeometry.ParametricCramerRaoAndCumulants

open Finset
open scoped BigOperators
open InfoGeometry.Epistemology.ChentsovMetricInvariance
open InfoGeometry.Analytic
open InfoGeometry.ExponentialFamily
open InfoGeometry.Convex
open InfoGeometry.Information
open InfoGeometry.InformationGeometry.ArakiDonald

/-! ### 1. Parametric Score, Variance, and Fisher Information -/

/-- Logarithmic score vector `∂_θ log p(x) = dp(x) / p(x)`. -/
def score {α : Type*} (p dp : α → ℝ) (x : α) : ℝ :=
  dp x / p x

/-- Sample expectation `∑ x, p(x) T(x)` on a finite sample space. -/
def statMeanOf {α : Type*} [Fintype α] (p T : α → ℝ) : ℝ :=
  ∑ x, p x * T x

/-- Sample variance `∑ x, p(x) (T(x) - E_p[T])^2` on a finite sample space. -/
def statVariance {α : Type*} [Fintype α] (p T : α → ℝ) : ℝ :=
  ∑ x, p x * (T x - statMeanOf p T) ^ 2

/-- Parametric model Fisher information `E_P[(∂_θ log p)^2]`. -/
def modelFisherInfo {α : Type*} [Fintype α] (P : ProbInterior α) (dp : α → ℝ) : ℝ :=
  ∑ x, P.p x * (score P.p dp x) ^ 2

theorem modelFisherInfo_nonneg {α : Type*} [Fintype α] (P : ProbInterior α) (dp : α → ℝ) :
    0 ≤ modelFisherInfo P dp := by
  unfold modelFisherInfo
  refine Finset.sum_nonneg ?_
  intro x _
  exact mul_nonneg (P.pos x).le (sq_nonneg _)

theorem statVariance_nonneg {α : Type*} [Fintype α] (P : ProbInterior α) (T : α → ℝ) :
    0 ≤ statVariance P.p T := by
  unfold statVariance
  refine Finset.sum_nonneg ?_
  intro x _
  exact mul_nonneg (P.pos x).le (sq_nonneg _)

/-- On positive probabilities, differentiating `Real.log (p t x)` yields `score (p θ) dp x`. -/
theorem hasDerivAt_log_prob_eq_score {α : Type*} (p : ℝ → α → ℝ) (dp : α → ℝ) (θ : ℝ) (x : α)
    (hpos : 0 < p θ x) (hderiv : HasDerivAt (fun t => p t x) (dp x) θ) :
    HasDerivAt (fun t => Real.log (p t x)) (score (p θ) dp x) θ := by
  simpa [score] using hderiv.log (ne_of_gt hpos)

/-- Differentiating the normalization constraint `∑ x, p t x = 1` forces `∑ x, dp x = 0`. -/
theorem deriv_prob_sum_eq_zero {α : Type*} [Fintype α]
    (p : ℝ → α → ℝ) (dp : α → ℝ) (θ : ℝ)
    (hsum : ∀ t, ∑ x, p t x = 1)
    (hderiv : ∀ x, HasDerivAt (fun t => p t x) (dp x) θ) :
    ∑ x, dp x = 0 := by
  have hsum_deriv : HasDerivAt (fun t => ∑ x, p t x) (∑ x, dp x) θ :=
    HasDerivAt.fun_sum (fun x _ => hderiv x)
  have hfun : (fun t => ∑ x, p t x) = fun _ => (1 : ℝ) := funext hsum
  have hzero : HasDerivAt (fun t => ∑ x, p t x) 0 θ := by
    simpa [hfun] using (hasDerivAt_const θ (1 : ℝ))
  exact hsum_deriv.unique hzero

/-- Packaging a derivative profile `dp` with zero total mass as a `TangentVector`. -/
def tangentOfDeriv {α : Type*} [Fintype α] (dp : α → ℝ) (hzero : ∑ x, dp x = 0) :
    TangentVector α where
  v := dp
  sum_zero := hzero

/-- The score has expectation zero whenever `∑ x, dp x = 0`. -/
theorem expectation_score_eq_zero {α : Type*} [Fintype α]
    (P : ProbInterior α) (dp : α → ℝ) (hzero : ∑ x, dp x = 0) :
    ∑ x, P.p x * score P.p dp x = 0 := by
  unfold score
  calc
    ∑ x, P.p x * (dp x / P.p x) = ∑ x, dp x := by
      refine Finset.sum_congr rfl ?_
      intro x _
      exact mul_div_cancel₀ (dp x) (ne_of_gt (P.pos x))
    _ = 0 := hzero

/-- Model Fisher information agrees identically with `ChentsovMetricInvariance.fisherMetric`. -/
theorem modelFisherInfo_eq_chentsov_fisherMetric {α : Type*} [Fintype α]
    (P : ProbInterior α) (dp : α → ℝ) :
    modelFisherInfo P dp = fisherMetric P dp dp := by
  unfold modelFisherInfo score
  rw [fisherMetric_eq_score_expectation]
  refine Finset.sum_congr rfl ?_
  intro x _
  ring

lemma sum_dp_mul_eq_centered_score_pairing {α : Type*} [Fintype α]
    (P : ProbInterior α) (dp T : α → ℝ) (hzero : ∑ x, dp x = 0) :
    ∑ x, P.p x * ((T x - statMeanOf P.p T) * score P.p dp x) = ∑ x, dp x * T x := by
  calc
    ∑ x, P.p x * ((T x - statMeanOf P.p T) * score P.p dp x)
        = ∑ x, (dp x * T x - statMeanOf P.p T * dp x) := by
          refine Finset.sum_congr rfl ?_
          intro x _
          have hpne : P.p x ≠ 0 := ne_of_gt (P.pos x)
          unfold score
          field_simp [hpne]
    _ = (∑ x, dp x * T x) - statMeanOf P.p T * (∑ x, dp x) := by
          rw [Finset.sum_sub_distrib, Finset.mul_sum]
    _ = ∑ x, dp x * T x := by rw [hzero, mul_zero, sub_zero]

/-- Derivative of the sample expectation equals the covariance of `T` with the score. -/
theorem hasDerivAt_expectation_eq_covariance_score {α : Type*} [Fintype α]
    (p : ℝ → α → ℝ) (dp : α → ℝ) (θ : ℝ)
    (P : ProbInterior α) (hpθ : P.p = p θ)
    (hsum : ∀ t, ∑ x, p t x = 1)
    (hderiv : ∀ x, HasDerivAt (fun t => p t x) (dp x) θ)
    (T : α → ℝ) :
    HasDerivAt (fun t => statMeanOf (p t) T)
      (∑ x, p θ x * ((T x - statMeanOf (p θ) T) * score (p θ) dp x)) θ := by
  have hzero : ∑ x, dp x = 0 := deriv_prob_sum_eq_zero p dp θ hsum hderiv
  have hlin : HasDerivAt (fun t => ∑ x, p t x * T x) (∑ x, dp x * T x) θ :=
    HasDerivAt.fun_sum (fun x _ => (hderiv x).mul_const (T x))
  have hcov :
      ∑ x, p θ x * ((T x - statMeanOf (p θ) T) * score (p θ) dp x) = ∑ x, dp x * T x := by
    rw [← hpθ]
    exact sum_dp_mul_eq_centered_score_pairing P dp T hzero
  rw [hcov]
  simpa [statMeanOf] using hlin

/-! ### 2. Weighted Cauchy–Schwarz and Exact Saturation -/

/-- Finite non-negatively weighted Cauchy–Schwarz inequality. -/
theorem weighted_cauchy_schwarz {α : Type*} [Fintype α]
    (w f g : α → ℝ) (hw : ∀ x, 0 ≤ w x) :
    (∑ x, w x * (f x * g x)) ^ 2 ≤ (∑ x, w x * f x ^ 2) * (∑ x, w x * g x ^ 2) := by
  let c : ℝ := ∑ x, w x * (f x * g x)
  let sf : ℝ := ∑ x, w x * f x ^ 2
  let sg : ℝ := ∑ x, w x * g x ^ 2
  change c ^ 2 ≤ sf * sg
  have hsf_nonneg : 0 ≤ sf := Finset.sum_nonneg (fun x _ => mul_nonneg (hw x) (sq_nonneg _))
  have hsg_nonneg : 0 ≤ sg := Finset.sum_nonneg (fun x _ => mul_nonneg (hw x) (sq_nonneg _))
  have hres_nonneg : 0 ≤ ∑ x, w x * (sg * f x - c * g x) ^ 2 :=
    Finset.sum_nonneg (fun x _ => mul_nonneg (hw x) (sq_nonneg _))
  have hres_expand :
      ∑ x, w x * (sg * f x - c * g x) ^ 2 = sg * (sg * sf - c ^ 2) := by
    calc
      ∑ x, w x * (sg * f x - c * g x) ^ 2
          = ∑ x, (sg ^ 2 * (w x * f x ^ 2) - 2 * sg * c * (w x * (f x * g x)) +
              c ^ 2 * (w x * g x ^ 2)) := by
            refine Finset.sum_congr rfl ?_
            intro x _
            ring
      _ = sg ^ 2 * sf - 2 * sg * c * c + c ^ 2 * sg := by
            rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
              ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum]
      _ = sg * (sg * sf - c ^ 2) := by ring
  rcases lt_or_eq_of_le hsg_nonneg with hsg_pos | hsg_zero
  · rw [hres_expand] at hres_nonneg
    have hquad : 0 ≤ sg * sf - c ^ 2 := nonneg_of_mul_nonneg_right hres_nonneg hsg_pos
    linarith
  · have hg_terms : ∀ x ∈ (Finset.univ : Finset α), 0 ≤ w x * g x ^ 2 :=
      fun x _ => mul_nonneg (hw x) (sq_nonneg _)
    have hg_zero : ∀ x ∈ (Finset.univ : Finset α), w x * g x ^ 2 = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg hg_terms).mp hsg_zero.symm
    have hc_zero : c = 0 := by
      dsimp [c]
      refine Finset.sum_eq_zero ?_
      intro x hx
      have hxg := mul_eq_zero.mp (hg_zero x hx)
      rcases hxg with hwx | hgx
      · simp [hwx]
      · have hgx0 : g x = 0 := sq_eq_zero_iff.mp hgx
        simp [hgx0]
    rw [hc_zero, ← hsg_zero]
    simp

/-- Exact equality characterization for strictly positively weighted Cauchy–Schwarz when
`∑ x, w x * g x ^ 2 > 0`. -/
theorem weighted_cauchy_schwarz_eq_iff {α : Type*} [Fintype α]
    (w f g : α → ℝ) (hw : ∀ x, 0 < w x) (hsg : 0 < ∑ x, w x * g x ^ 2) :
    (∑ x, w x * (f x * g x)) ^ 2 = (∑ x, w x * f x ^ 2) * (∑ x, w x * g x ^ 2) ↔
      ∀ x, (∑ y, w y * g y ^ 2) * f x = (∑ y, w y * (f y * g y)) * g x := by
  let c : ℝ := ∑ x, w x * (f x * g x)
  let sf : ℝ := ∑ x, w x * f x ^ 2
  let sg : ℝ := ∑ x, w x * g x ^ 2
  have hres_expand :
      ∑ x, w x * (sg * f x - c * g x) ^ 2 = sg * (sg * sf - c ^ 2) := by
    calc
      ∑ x, w x * (sg * f x - c * g x) ^ 2
          = ∑ x, (sg ^ 2 * (w x * f x ^ 2) - 2 * sg * c * (w x * (f x * g x)) +
              c ^ 2 * (w x * g x ^ 2)) := by
            refine Finset.sum_congr rfl ?_
            intro x _
            ring
      _ = sg ^ 2 * sf - 2 * sg * c * c + c ^ 2 * sg := by
            rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
              ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum]
      _ = sg * (sg * sf - c ^ 2) := by ring
  have h_nonneg : ∀ x ∈ (Finset.univ : Finset α), 0 ≤ w x * (sg * f x - c * g x) ^ 2 :=
    fun x _ => mul_nonneg (hw x).le (sq_nonneg _)
  change c ^ 2 = sf * sg ↔ ∀ x, sg * f x = c * g x
  constructor
  · intro heq x
    have hsum0 : ∑ y, w y * (sg * f y - c * g y) ^ 2 = 0 := by
      rw [hres_expand, show sg * sf = sf * sg by ring, heq, sub_self, mul_zero]
    have hterm0 := (Finset.sum_eq_zero_iff_of_nonneg h_nonneg).mp hsum0 x (Finset.mem_univ x)
    have hsq0 : (sg * f x - c * g x) ^ 2 = 0 :=
      (mul_eq_zero.mp hterm0).resolve_left (ne_of_gt (hw x))
    exact sub_eq_zero.mp (sq_eq_zero_iff.mp hsq0)
  · intro haff
    have hsum0 : ∑ y, w y * (sg * f y - c * g y) ^ 2 = 0 := by
      refine Finset.sum_eq_zero ?_
      intro y _
      rw [haff y, sub_self, sq, mul_zero, mul_zero]
    rw [hres_expand] at hsum0
    have hdiff0 : sg * sf - c ^ 2 = 0 := (mul_eq_zero.mp hsum0).resolve_left (ne_of_gt hsg)
    linarith

/-! ### 3. Genuine Cramér–Rao Inequality and Affine-Score Saturation -/

/-- Finite-sample Cramér–Rao covariance inequality:
`(∑ x, dp x * T x)^2 ≤ Var_P(T) * I_F(P, dp)`. -/
theorem cramer_rao_covariance_bound {α : Type*} [Fintype α]
    (P : ProbInterior α) (dp T : α → ℝ) (hzero : ∑ x, dp x = 0) :
    (∑ x, dp x * T x) ^ 2 ≤ statVariance P.p T * modelFisherInfo P dp := by
  have hcs := weighted_cauchy_schwarz P.p
    (fun x => T x - statMeanOf P.p T) (score P.p dp) (fun x => (P.pos x).le)
  rw [sum_dp_mul_eq_centered_score_pairing P dp T hzero] at hcs
  exact hcs

/-- Differentiable statistical-model Cramér–Rao inequality:
`(d/dθ E_{p(θ)}[T])^2 ≤ Var_{p(θ)}(T) * I_F(p(θ), dp)`. -/
theorem cramer_rao_hasDerivAt_bound {α : Type*} [Fintype α]
    (p : ℝ → α → ℝ) (dp : α → ℝ) (θ : ℝ)
    (P : ProbInterior α) (hpθ : P.p = p θ)
    (hsum : ∀ t, ∑ x, p t x = 1)
    (hderiv : ∀ x, HasDerivAt (fun t => p t x) (dp x) θ)
    (T : α → ℝ) (dμ : ℝ)
    (hdμ : HasDerivAt (fun t => statMeanOf (p t) T) dμ θ) :
    dμ ^ 2 ≤ statVariance (p θ) T * modelFisherInfo P dp := by
  have hzero : ∑ x, dp x = 0 := deriv_prob_sum_eq_zero p dp θ hsum hderiv
  have hcov := hasDerivAt_expectation_eq_covariance_score p dp θ P hpθ hsum hderiv T
  rw [← hpθ] at hcov
  have heq : dμ = ∑ x, dp x * T x := by
    rw [hdμ.unique hcov, sum_dp_mul_eq_centered_score_pairing P dp T hzero]
  rw [heq, ← hpθ]
  exact cramer_rao_covariance_bound P dp T hzero

/-- Unbiased-estimator Cramér–Rao lower bound: if `d/dθ E_{p(θ)}[T] = 1` and
`0 < modelFisherInfo P dp`, then `1 / modelFisherInfo P dp ≤ Var_{p(θ)}(T)`. -/
theorem cramer_rao_unbiased_lower_bound {α : Type*} [Fintype α]
    (p : ℝ → α → ℝ) (dp : α → ℝ) (θ : ℝ)
    (P : ProbInterior α) (hpθ : P.p = p θ)
    (hsum : ∀ t, ∑ x, p t x = 1)
    (hderiv : ∀ x, HasDerivAt (fun t => p t x) (dp x) θ)
    (T : α → ℝ)
    (hunbiased : HasDerivAt (fun t => statMeanOf (p t) T) 1 θ)
    (hI : 0 < modelFisherInfo P dp) :
    1 / modelFisherInfo P dp ≤ statVariance (p θ) T := by
  have hcr := cramer_rao_hasDerivAt_bound p dp θ P hpθ hsum hderiv T 1 hunbiased
  rw [one_pow] at hcr
  exact (div_le_iff₀ hI).mpr hcr

/-- Exact saturation characterization for the Cramér–Rao inequality when
`0 < modelFisherInfo P dp`: equality holds iff the centered estimator is proportional
to the score. -/
theorem cramer_rao_saturated_iff_affine_score {α : Type*} [Fintype α]
    (P : ProbInterior α) (dp T : α → ℝ) (hzero : ∑ x, dp x = 0)
    (hI : 0 < modelFisherInfo P dp) :
    (∑ x, dp x * T x) ^ 2 = statVariance P.p T * modelFisherInfo P dp ↔
      ∀ x, T x - statMeanOf P.p T =
        ((∑ y, dp y * T y) / modelFisherInfo P dp) * score P.p dp x := by
  have hcs := weighted_cauchy_schwarz_eq_iff P.p
    (fun x => T x - statMeanOf P.p T) (score P.p dp) P.pos hI
  rw [sum_dp_mul_eq_centered_score_pairing P dp T hzero] at hcs
  have hcs' : (∑ x, dp x * T x) ^ 2 = statVariance P.p T * modelFisherInfo P dp ↔
      ∀ x, modelFisherInfo P dp * (T x - statMeanOf P.p T) = (∑ y, dp y * T y) * score P.p dp x := by
    simpa [statVariance, modelFisherInfo] using hcs
  rw [hcs']
  have hIne : modelFisherInfo P dp ≠ 0 := ne_of_gt hI
  constructor
  · intro h x
    calc
      T x - statMeanOf P.p T
          = (modelFisherInfo P dp * (T x - statMeanOf P.p T)) / modelFisherInfo P dp := by
              field_simp [hIne]
      _ = ((∑ y, dp y * T y) * score P.p dp x) / modelFisherInfo P dp := by rw [h x]
      _ = ((∑ y, dp y * T y) / modelFisherInfo P dp) * score P.p dp x := by ring
  · intro h x
    calc
      modelFisherInfo P dp * (T x - statMeanOf P.p T)
          = modelFisherInfo P dp *
              (((∑ y, dp y * T y) / modelFisherInfo P dp) * score P.p dp x) := by rw [h x]
      _ = (∑ y, dp y * T y) * score P.p dp x := by
            field_simp [hIne]

/-- Discharging `CramerRaoUncertainty.heisenberg_from_cramer_rao` directly from a
differentiable unbiased statistical model without assuming `VarX * I_F ≥ 1`. -/
theorem heisenberg_from_parametric_cramer_rao {α : Type*} [Fintype α]
    (p : ℝ → α → ℝ) (dp : α → ℝ) (θ : ℝ)
    (P : ProbInterior α) (hpθ : P.p = p θ)
    (hsum : ∀ t, ∑ x, p t x = 1)
    (hderiv : ∀ x, HasDerivAt (fun t => p t x) (dp x) θ)
    (T : α → ℝ)
    (hunbiased : HasDerivAt (fun t => statMeanOf (p t) T) 1 θ)
    (VarP : ℝ) (h_momentum_var : VarP = (1 / 4) * modelFisherInfo P dp) :
    statVariance (p θ) T * VarP ≥ 1 / 4 := by
  have hcr := cramer_rao_hasDerivAt_bound p dp θ P hpθ hsum hderiv T 1 hunbiased
  rw [one_pow] at hcr
  exact InfoGeometry.Canonical.CramerRaoUncertainty.heisenberg_from_cramer_rao
    (statVariance (p θ) T) VarP (modelFisherInfo P dp) hcr h_momentum_var

/-! ### 4. Unconditional Exponential-Family Cumulants & Strict Convexity -/

section ExponentialFamilyUnconditional

variable {α : Type _} [Fintype α] [Nonempty α]

/-- Unnormalized positive weights underlying `FiniteExponentialFamilyData`. -/
noncomputable def familyBaseWeights (F : FiniteExponentialFamilyData α) (x : α) : ℝ :=
  (F.base x).toReal

omit [Nonempty α] in
lemma familyPartition_eq_logSumExpPartition (F : FiniteExponentialFamilyData α) (θ : ℝ) :
    familyPartition F θ = logSumExpPartition (familyBaseWeights F) F.stat θ := rfl

omit [Nonempty α] in
lemma familyLogPartition_eq_logSumExp (F : FiniteExponentialFamilyData α) (θ : ℝ) :
    familyLogPartition F θ = logSumExp (familyBaseWeights F) F.stat θ := rfl

omit [Nonempty α] in
lemma familyDensity_eq_logSumExpWeight (F : FiniteExponentialFamilyData α) (θ : ℝ) (x : α) :
    familyDensity F θ x = logSumExpWeight (familyBaseWeights F) F.stat θ x := rfl

/-- Interior distribution package for a finite exponential family at `θ`. -/
noncomputable def familyProbInterior (F : FiniteExponentialFamilyData α) (θ : ℝ) :
    ProbInterior α where
  p := familyDensity F θ
  pos := familyDensity_pos F θ
  sum_one := familyNormalization F θ

lemma familyStatMean_eq_logSumExpMean (F : FiniteExponentialFamilyData α) (θ : ℝ) :
    ExponentialFamily.statMean F θ = logSumExpMean (familyBaseWeights F) F.stat θ := by
  rw [logSumExpMean_eq_weighted_sum (familyBaseWeights F) F.stat F.base_pos θ]
  rfl

/-- Unconditional first cumulant identity: `ψ'(θ) = E_θ[T]`. -/
theorem deriv_familyLogPartition_eq_statMean (F : FiniteExponentialFamilyData α) (θ : ℝ) :
    deriv (familyLogPartition F) θ = ExponentialFamily.statMean F θ := by
  have hfn : familyLogPartition F = logSumExp (familyBaseWeights F) F.stat :=
    funext (familyLogPartition_eq_logSumExp F)
  rw [hfn, logSumExp_deriv_eq_mean (familyBaseWeights F) F.stat F.base_pos θ,
    familyStatMean_eq_logSumExpMean]

/-- Unconditional KL–Bregman duality, discharging the `hmean` hypothesis of
`ExponentialFamily.KLBregman`. -/
theorem KLParam_eq_bregman_unconditional (F : FiniteExponentialFamilyData α) (θ η : ℝ) :
    KLParam F θ η = (ExponentialFamily.logPotential F).bregman η θ :=
  KLParam_eq_LogPotential_bregman_of_statMean_eq_deriv F θ η
    (deriv_familyLogPartition_eq_statMean F θ).symm

/-- Unconditional KL non-negativity for a 1D exponential family. -/
theorem KLParam_nonneg (F : FiniteExponentialFamilyData α) (θ η : ℝ) :
    0 ≤ KLParam F θ η := by
  let _ : DecidableEq α := Classical.decEq α
  unfold KLParam
  have hkl :
      ∑ x, familyDensity F θ x *
          (Real.log (familyDensity F θ x) - Real.log (familyDensity F η x)) =
        relativeEntropy (familyDensity F θ) (familyDensity F η) := by
    unfold relativeEntropy
    refine Finset.sum_congr rfl ?_
    intro x _
    rw [Real.log_div (ne_of_gt (familyDensity_pos F θ x)) (ne_of_gt (familyDensity_pos F η x))]
  rw [hkl]
  exact relative_entropy_nonneg_of_donald (familyDensity F θ) (familyDensity F η)
    (familyDensity_pos F θ) (familyDensity_pos F η)
    (familyNormalization F θ) (familyNormalization F η)

/-- Derivative of the exponential-family density at parameter `θ`. -/
theorem hasDerivAt_familyDensity (F : FiniteExponentialFamilyData α) (θ : ℝ) (x : α) :
    HasDerivAt (fun t => familyDensity F t x)
      (familyDensity F θ x * (F.stat x - ExponentialFamily.statMean F θ)) θ := by
  have hpart := hasDerivAt_logSumExpPartition (familyBaseWeights F) F.stat θ
  have hterm := hasDerivAt_logSumExpPartition_term (familyBaseWeights F) F.stat x θ
  have hZne : logSumExpPartition (familyBaseWeights F) F.stat θ ≠ 0 :=
    (logSumExp_sum_pos (familyBaseWeights F) F.stat F.base_pos θ).ne'
  have hquot := hterm.div hpart hZne
  have hval :
      (familyBaseWeights F x * (F.stat x * Real.exp (θ * F.stat x)) *
            logSumExpPartition (familyBaseWeights F) F.stat θ -
          familyBaseWeights F x * Real.exp (θ * F.stat x) *
            logSumExpMoment1 (familyBaseWeights F) F.stat θ) /
          logSumExpPartition (familyBaseWeights F) F.stat θ ^ (2 : ℕ) =
        familyDensity F θ x * (F.stat x - ExponentialFamily.statMean F θ) := by
    rw [familyStatMean_eq_logSumExpMean]
    unfold familyDensity familyBaseWeights familyPartition logSumExpMean
      logSumExpMoment1 logSumExpPartition at *
    field_simp [hZne]
  rw [hval] at hquot
  exact hquot

/-- Exact exponential-family score of the natural parameter equals `T(x) - E_θ[T]`. -/
theorem familyScore_eq_centeredStat (F : FiniteExponentialFamilyData α) (θ : ℝ) (x : α) :
    score (familyDensity F θ)
      (fun y => familyDensity F θ y * (F.stat y - ExponentialFamily.statMean F θ)) x =
      F.stat x - ExponentialFamily.statMean F θ := by
  unfold score
  have hpos : familyDensity F θ x ≠ 0 := ne_of_gt (familyDensity_pos F θ x)
  field_simp [hpos]

/-- Unconditional second cumulant identity: `ψ''(θ) = Var_θ(T)`. -/
theorem deriv2_familyLogPartition_eq_statVariance (F : FiniteExponentialFamilyData α) (θ : ℝ) :
    deriv (fun t => deriv (familyLogPartition F) t) θ = statVariance (familyDensity F θ) F.stat := by
  have hfn : familyLogPartition F = logSumExp (familyBaseWeights F) F.stat :=
    funext (familyLogPartition_eq_logSumExp F)
  rw [hfn, logSumExp_secondDeriv_eq_variance (familyBaseWeights F) F.stat F.base_pos θ,
    logSumExpVariance_eq_centered (familyBaseWeights F) F.stat F.base_pos θ]
  unfold statVariance statMeanOf
  refine Finset.sum_congr rfl ?_
  intro x _
  have hm : ∑ j, logSumExpWeight (familyBaseWeights F) F.stat θ j * F.stat j =
      ∑ y, familyDensity F θ y * F.stat y := by
    refine Finset.sum_congr rfl ?_
    intro y _
    rw [← familyDensity_eq_logSumExpWeight]
  rw [← familyDensity_eq_logSumExpWeight, hm]

/-- Second derivative equals the model Fisher information of `F` at `θ`. -/
theorem deriv2_familyLogPartition_eq_modelFisherInfo (F : FiniteExponentialFamilyData α) (θ : ℝ) :
    deriv (fun t => deriv (familyLogPartition F) t) θ =
      modelFisherInfo (familyProbInterior F θ)
        (fun x => familyDensity F θ x * (F.stat x - ExponentialFamily.statMean F θ)) := by
  rw [deriv2_familyLogPartition_eq_statVariance]
  unfold statVariance statMeanOf modelFisherInfo familyProbInterior
  refine Finset.sum_congr rfl ?_
  intro x _
  rw [familyScore_eq_centeredStat]
  rfl

/-- Sufficient statistic `F.stat` attains exact Cramér–Rao equality at every `θ`. -/
theorem sufficient_statistic_saturates_cramer_rao (F : FiniteExponentialFamilyData α) (θ : ℝ) :
    let dp := fun x => familyDensity F θ x * (F.stat x - ExponentialFamily.statMean F θ)
    (∑ x, dp x * F.stat x) ^ 2 =
      statVariance (familyDensity F θ) F.stat * modelFisherInfo (familyProbInterior F θ) dp := by
  intro dp
  have hcov : ∑ x, dp x * F.stat x = statVariance (familyDensity F θ) F.stat := by
    have hm : statMeanOf (familyDensity F θ) F.stat = ExponentialFamily.statMean F θ := rfl
    have hz : ∑ x, dp x = 0 :=
      deriv_prob_sum_eq_zero (familyDensity F) dp θ (familyNormalization F)
        (hasDerivAt_familyDensity F θ)
    calc
      ∑ x, dp x * F.stat x
          = ∑ x, dp x * F.stat x - ExponentialFamily.statMean F θ * ∑ x, dp x := by
              rw [hz, mul_zero, sub_zero]
      _ = ∑ x, familyDensity F θ x * (F.stat x - ExponentialFamily.statMean F θ) ^ 2 := by
            rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
            refine Finset.sum_congr rfl ?_
            intro x _
            dsimp [dp]
            ring
      _ = statVariance (familyDensity F θ) F.stat := rfl
  have hfi : modelFisherInfo (familyProbInterior F θ) dp =
      statVariance (familyDensity F θ) F.stat := by
    rw [← deriv2_familyLogPartition_eq_modelFisherInfo,
      deriv2_familyLogPartition_eq_statVariance]
  rw [hcov, hfi, sq]

end ExponentialFamilyUnconditional

section StrictConvexLogSumExp

/-- Variance of nonconstant slopes under strictly positive Gibbs weights is strictly positive. -/
theorem logSumExpVariance_pos_of_nonconstant
    {ι : Type _} [Fintype ι] [Nonempty ι]
    (w a : ι → ℝ) (hw : ∀ i, 0 < w i)
    (hnc : ∃ i j : ι, a i ≠ a j) (θ : ℝ) :
    0 < logSumExpVariance w a θ := by
  rw [logSumExpVariance_eq_centered w a hw θ]
  let p : ι → ℝ := fun i => logSumExpWeight w a θ i
  let m : ℝ := ∑ j, p j * a j
  have hnonneg : ∀ i ∈ (Finset.univ : Finset ι), 0 ≤ p i * (a i - m) ^ (2 : ℕ) :=
    fun i _ => mul_nonneg (logSumExpWeight_pos w a hw θ i).le (sq_nonneg _)
  rcases hnc with ⟨i₀, j₀, hij⟩
  have hne : a i₀ ≠ m ∨ a j₀ ≠ m := by
    by_contra hboth
    push Not at hboth
    exact hij (hboth.1.trans hboth.2.symm)
  have hex : ∃ i ∈ (Finset.univ : Finset ι), 0 < p i * (a i - m) ^ (2 : ℕ) := by
    rcases hne with hi | hj
    · exact ⟨i₀, Finset.mem_univ i₀,
        mul_pos (logSumExpWeight_pos w a hw θ i₀) (sq_pos_of_ne_zero (sub_ne_zero.mpr hi))⟩
    · exact ⟨j₀, Finset.mem_univ j₀,
        mul_pos (logSumExpWeight_pos w a hw θ j₀) (sq_pos_of_ne_zero (sub_ne_zero.mpr hj))⟩
  exact Finset.sum_pos' hnonneg hex

/-- Unconditional strict convexity of `logSumExp w a` on `ℝ` whenever slopes `a` are nonconstant. -/
theorem logSumExp_strictConvexOn_of_nonconstant
    {ι : Type _} [Fintype ι] [Nonempty ι]
    (w a : ι → ℝ) (hw : ∀ i, 0 < w i)
    (hnc : ∃ i j : ι, a i ≠ a j) :
    StrictConvexOn ℝ Set.univ (logSumExp w a) := by
  refine strictConvexOn_univ_of_deriv2_pos (logSumExp_contDiff w a hw).continuous ?_
  intro θ
  change 0 < deriv (fun t => deriv (logSumExp w a) t) θ
  rw [logSumExp_secondDeriv_eq_variance w a hw θ]
  exact logSumExpVariance_pos_of_nonconstant w a hw hnc θ

/-- Unconditional construction of `Convex.LegendrePotential` from any finite log-sum-exp
data with nonconstant sufficient statistics, discharging `hstrict` in
`ExponentialFamily.Legendre`. -/
noncomputable def logSumExpLegendre_of_nonconstant
    {ι : Type _} [Fintype ι] [Nonempty ι]
    (w a : ι → ℝ) (hw : ∀ i, 0 < w i)
    (hnc : ∃ i j : ι, a i ≠ a j) :
    LegendrePotential :=
  logSumExpLegendre w a hw (logSumExp_strictConvexOn_of_nonconstant w a hw hnc)

end StrictConvexLogSumExp

/-! ### 5. Multivariate `Information.FiniteExpFamily`: Directional Cumulants & Pythagorean Law -/

section MultivariateExpFamily

variable {α : Type _} [Fintype α] [Nonempty α]

/-- Kullback–Leibler divergence between two natural-parameter members of a multivariate
finite exponential family `F`. -/
def multiKL {d : ℕ} (F : FiniteExpFamily (α := α) d) (θ η : Fin d → ℝ) : ℝ :=
  relativeEntropy (Information.density F θ) (Information.density F η)

lemma log_multiDensity_eq {d : ℕ} (F : FiniteExpFamily (α := α) d) (θ : Fin d → ℝ) (x : α) :
    Real.log (Information.density F θ x) =
      Information.naturalParam F θ x + Real.log (F.base x) - Information.logPartition F θ := by
  unfold Information.density Information.logPartition
  have h1 : Real.exp (Information.naturalParam F θ x) * F.base x ≠ 0 :=
    ne_of_gt (mul_pos (Real.exp_pos _) (F.base_pos x))
  have hZ : Information.partition F θ ≠ 0 := ne_of_gt (Information.partition_pos F θ)
  rw [Real.log_div h1 hZ, Real.log_mul (ne_of_gt (Real.exp_pos _)) (ne_of_gt (F.base_pos x)),
    Real.log_exp]

/-- Canonical Bregman-gap identity for multivariate exponential families:
`KL(P_θ ∥ P_η) = ψ(η) - ψ(θ) - ⟨η - θ, E_θ[T]⟩`. -/
theorem multiKL_eq_potential_gap {d : ℕ} (F : FiniteExpFamily (α := α) d) (θ η : Fin d → ℝ) :
    multiKL F θ η =
      Information.logPartition F η - Information.logPartition F θ -
        ∑ i, (η i - θ i) * Information.statMean F θ i := by
  unfold multiKL relativeEntropy
  calc
    ∑ x, Information.density F θ x *
        Real.log (Information.density F θ x / Information.density F η x)
        = ∑ x, Information.density F θ x *
            (Real.log (Information.density F θ x) - Real.log (Information.density F η x)) := by
            refine Finset.sum_congr rfl ?_
            intro x _
            rw [Real.log_div (ne_of_gt (Information.density_pos F θ x))
              (ne_of_gt (Information.density_pos F η x))]
    _ = ∑ x, Information.density F θ x *
            ((∑ i, (θ i - η i) * F.stat x i) -
              (Information.logPartition F θ - Information.logPartition F η)) := by
            refine Finset.sum_congr rfl ?_
            intro x _
            rw [log_multiDensity_eq F θ x, log_multiDensity_eq F η x]
            unfold Information.naturalParam
            have hlin : (∑ i, θ i * F.stat x i) - (∑ i, η i * F.stat x i) =
                ∑ i, (θ i - η i) * F.stat x i := by
              rw [← Finset.sum_sub_distrib]
              refine Finset.sum_congr rfl ?_
              intro i _
              ring
            calc
              Information.density F θ x *
                  (∑ i, θ i * F.stat x i + Real.log (F.base x) - Information.logPartition F θ -
                    (∑ i, η i * F.stat x i + Real.log (F.base x) - Information.logPartition F η))
                  = Information.density F θ x *
                      (((∑ i, θ i * F.stat x i) - ∑ i, η i * F.stat x i) -
                        (Information.logPartition F θ - Information.logPartition F η)) := by
                    ring
              _ = Information.density F θ x *
                    ((∑ i, (θ i - η i) * F.stat x i) -
                      (Information.logPartition F θ - Information.logPartition F η)) := by
                    rw [hlin]
    _ = ∑ x, (Information.density F θ x * ∑ i, (θ i - η i) * F.stat x i) -
          ∑ x, (Information.logPartition F θ - Information.logPartition F η) *
            Information.density F θ x := by
          rw [← Finset.sum_sub_distrib]
          refine Finset.sum_congr rfl ?_
          intro x _
          ring
    _ = (∑ i, (θ i - η i) * Information.statMean F θ i) -
          (Information.logPartition F θ - Information.logPartition F η) := by
          have h1 :
              (∑ x, Information.density F θ x * ∑ i, (θ i - η i) * F.stat x i) =
                ∑ i, (θ i - η i) * Information.statMean F θ i := by
            simpa [Information.expectation, Information.linearStat] using
              (expectation_linearStat F θ (fun i => θ i - η i))
          have h2 :
              ∑ x, (Information.logPartition F θ - Information.logPartition F η) *
                Information.density F θ x =
                Information.logPartition F θ - Information.logPartition F η := by
            rw [← Finset.mul_sum, Information.density_sum_one F θ, mul_one]
          rw [h1, h2]
    _ = Information.logPartition F η - Information.logPartition F θ -
          ∑ i, (η i - θ i) * Information.statMean F θ i := by
          have hneg :
              ∑ i, (θ i - η i) * Information.statMean F θ i =
                - ∑ i, (η i - θ i) * Information.statMean F θ i := by
            rw [← Finset.sum_neg_distrib]
            refine Finset.sum_congr rfl ?_
            intro i _
            ring
          rw [hneg]
          ring

/-- Multivariate KL divergence is always non-negative. -/
theorem multiKL_nonneg {d : ℕ} (F : FiniteExpFamily (α := α) d) (θ η : Fin d → ℝ) :
    0 ≤ multiKL F θ η := by
  let _ : DecidableEq α := Classical.decEq α
  exact relative_entropy_nonneg_of_donald (Information.density F θ) (Information.density F η)
    (fun x => Information.density_pos F θ x) (fun x => Information.density_pos F η x)
    (Information.density_sum_one F θ) (Information.density_sum_one F η)

/-- Exact Amari three-point identity in dual exponential/mixture coordinates for `multiKL`. -/
theorem multiKL_three_point_identity {d : ℕ} (F : FiniteExpFamily (α := α) d)
    (θ μ η : Fin d → ℝ) :
    multiKL F θ η =
      multiKL F θ μ + multiKL F μ η +
        ∑ i, (μ i - η i) * (Information.statMean F θ i - Information.statMean F μ i) := by
  rw [multiKL_eq_potential_gap F θ η, multiKL_eq_potential_gap F θ μ, multiKL_eq_potential_gap F μ η]
  have hsum1 :
      (∑ i, (μ i - θ i) * Information.statMean F θ i) +
          (∑ i, (η i - μ i) * Information.statMean F μ i) -
          (∑ i, (μ i - η i) * (Information.statMean F θ i - Information.statMean F μ i)) =
        ∑ i, (η i - θ i) * Information.statMean F θ i := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl ?_
    intro i _
    ring
  linarith [hsum1]

/-- Amari's Mixed-Geodesic Pythagorean Theorem: whenever `(μ - η)` is dual-orthogonal
to `(E_θ[T] - E_μ[T])`, `KL(P_θ ∥ P_η) = KL(P_θ ∥ P_μ) + KL(P_μ ∥ P_η)`. -/
theorem multiKL_mixed_pythagorean {d : ℕ} (F : FiniteExpFamily (α := α) d)
    (θ μ η : Fin d → ℝ)
    (horth : ∑ i, (μ i - η i) * (Information.statMean F θ i - Information.statMean F μ i) = 0) :
    multiKL F θ η = multiKL F θ μ + multiKL F μ η := by
  rw [multiKL_three_point_identity F θ μ η, horth, add_zero]

/-- Weighted base measure anchored at `θ` for evaluating directional slices of
`Information.logPartition F`. -/
noncomputable def sliceBaseWeights {d : ℕ} (F : FiniteExpFamily (α := α) d)
    (θ : Fin d → ℝ) (x : α) : ℝ :=
  Real.exp (Information.naturalParam F θ x) * F.base x

omit [Fintype α] [Nonempty α] in
lemma sliceBaseWeights_pos {d : ℕ} (F : FiniteExpFamily (α := α) d) (θ : Fin d → ℝ) (x : α) :
    0 < sliceBaseWeights F θ x :=
  mul_pos (Real.exp_pos _) (F.base_pos x)

omit [Nonempty α] in
/-- Along any ray `t ↦ θ + t • v`, the multivariate log-partition reduces identically
to a 1D `Analytic.logSumExp` with slope `linearStat F v`. -/
theorem logPartition_slice_eq_logSumExp {d : ℕ} (F : FiniteExpFamily (α := α) d)
    (θ v : Fin d → ℝ) (t : ℝ) :
    Information.logPartition F (θ + t • v) =
      logSumExp (sliceBaseWeights F θ) (Information.linearStat F v) t := by
  unfold Information.logPartition Information.partition logSumExp logSumExpPartition sliceBaseWeights
  congr 1
  refine Finset.sum_congr rfl ?_
  intro x _
  have hnat : Information.naturalParam F (θ + t • v) x =
      Information.naturalParam F θ x + t * Information.linearStat F v x := by
    unfold Information.naturalParam Information.linearStat
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl ?_
    intro i _
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [hnat, Real.exp_add]
  ring

/-- Directional first cumulant: `d/dt|_{t=0} ψ(θ + t v) = ⟨v, E_θ[T]⟩`. -/
theorem hasDerivAt_logPartition_slice {d : ℕ} (F : FiniteExpFamily (α := α) d)
    (θ v : Fin d → ℝ) :
    HasDerivAt (fun t : ℝ => Information.logPartition F (θ + t • v))
      (∑ i, v i * Information.statMean F θ i) 0 := by
  have hfn :
      (fun t : ℝ => Information.logPartition F (θ + t • v)) =
        logSumExp (sliceBaseWeights F θ) (Information.linearStat F v) :=
    funext (logPartition_slice_eq_logSumExp F θ v)
  rw [hfn]
  have hd := hasDerivAt_logSumExp (sliceBaseWeights F θ) (Information.linearStat F v)
    (sliceBaseWeights_pos F θ) 0
  have hmean :
      logSumExpMean (sliceBaseWeights F θ) (Information.linearStat F v) 0 =
        ∑ i, v i * Information.statMean F θ i := by
    rw [logSumExpMean_eq_weighted_sum _ _ (sliceBaseWeights_pos F θ) 0,
      ← Information.expectation_linearStat F θ v]
    unfold Information.expectation
    refine Finset.sum_congr rfl ?_
    intro x _
    have hw :
        logSumExpWeight (sliceBaseWeights F θ) (Information.linearStat F v) 0 x =
          Information.density F θ x := by
      unfold logSumExpWeight logSumExpPartition sliceBaseWeights
        Information.density Information.partition
      simp
    rw [hw]
  rwa [hmean] at hd

/-- Directional second cumulant equals the multivariate Fisher quadratic form `vᵀ G(θ) v`. -/
theorem secondDeriv_logPartition_slice_eq_fisherQuadratic {d : ℕ}
    (F : FiniteExpFamily (α := α) d) (θ v : Fin d → ℝ) :
    deriv (fun t : ℝ => deriv (fun s : ℝ => Information.logPartition F (θ + s • v)) t) 0 =
      Information.fisherQuadratic F θ v := by
  have hfn :
      (fun s : ℝ => Information.logPartition F (θ + s • v)) =
        logSumExp (sliceBaseWeights F θ) (Information.linearStat F v) :=
    funext (logPartition_slice_eq_logSumExp F θ v)
  rw [hfn, logSumExp_secondDeriv_eq_variance _ _ (sliceBaseWeights_pos F θ) 0,
    logSumExpVariance_eq_centered _ _ (sliceBaseWeights_pos F θ) 0,
    Information.fisher_as_variance F θ v]
  unfold Information.expectation Information.centeredLinearStat
  refine Finset.sum_congr rfl ?_
  intro x _
  have hw : ∀ y : α,
      logSumExpWeight (sliceBaseWeights F θ) (Information.linearStat F v) 0 y =
        Information.density F θ y := by
    intro y
    unfold logSumExpWeight logSumExpPartition sliceBaseWeights
      Information.density Information.partition
    simp
  simp_rw [hw]
  rfl

end MultivariateExpFamily

end InfoGeometry.InformationGeometry.ParametricCramerRaoAndCumulants

end section
