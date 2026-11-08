/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Tactic
import InfoGeometry.Epistemology.ChentsovMetricInvariance

/-!
# The Fisher natural gradient is the direction of steepest ascent

Part A proves an abstract Cauchy–Schwarz steepest-ascent statement for a symmetric positive
semidefinite bilinear form. Part B constructs the explicit Fisher natural gradient
`n_a = P_a (ℓ_a - E_P ℓ)` of a covector `ℓ` on the interior of the probability simplex, shows that
it is the unique tangent Riesz representative of `w ↦ ∑ ℓ_a w_a` for the Fisher metric
(`ChentsovMetricInvariance.fisherMetric`), and that it maximises the first-order change among tangent
directions of no larger Fisher length. Its value is the variance `Var_P ℓ`.
-/

namespace InfoGeometry.Epistemology.FisherNaturalGradientSteepest

open Finset
open scoped BigOperators
open InfoGeometry.Epistemology.ChentsovMetricInvariance

/-! ### A. Abstract Cauchy–Schwarz steepest ascent -/

section Abstract

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- Cauchy–Schwarz for a symmetric positive semidefinite bilinear form. -/
theorem psd_cauchy_schwarz (g : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (hsymm : ∀ u v, g u v = g v u)
    (hpsd : ∀ u, 0 ≤ g u u) (n w : V) : g n w ^ 2 ≤ g n n * g w w := by
  have hquad : ∀ t : ℝ, 0 ≤ g w w * (t * t) + (-2 * g n w) * t + g n n := by
    intro t
    have h := hpsd (n - t • w)
    simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul] at h
    rw [hsymm w n] at h
    nlinarith [h]
  have hd := discrim_le_zero hquad
  unfold discrim at hd
  nlinarith [hd]

/-- Core comparison: a direction of no larger `g`-length has no larger pairing with `n`. -/
theorem pairing_le_of_quad_le (g : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (hsymm : ∀ u v, g u v = g v u)
    (hpsd : ∀ u, 0 ≤ g u u) (n w : V) (hw : g w w ≤ g n n) : g n w ≤ g n n := by
  have hcs := psd_cauchy_schwarz g hsymm hpsd n w
  have hnn := hpsd n
  have hww := hpsd w
  nlinarith [mul_le_mul_of_nonneg_left hw hnn]

/-- Lower comparison: `-g(n,n) ≤ g(n,w)` whenever `g(w,w) ≤ g(n,n)`. -/
theorem neg_quad_le_pairing (g : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (hsymm : ∀ u v, g u v = g v u)
    (hpsd : ∀ u, 0 ≤ g u u) (n w : V) (hw : g w w ≤ g n n) : -g n n ≤ g n w := by
  have h := pairing_le_of_quad_le g hsymm hpsd n (-w) (by simpa using hw)
  simp only [map_neg] at h
  linarith

/-- Steepest ascent: the `g`-representative `n` of `dL` maximises `dL` on the `g`-ball of
radius `‖n‖_g`. -/
theorem steepest_ascent (g : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (hsymm : ∀ u v, g u v = g v u)
    (hpsd : ∀ u, 0 ≤ g u u) (dL : V → ℝ) (n : V) (hrep : ∀ w, dL w = g n w) :
    ∀ w, g w w ≤ g n n → dL w ≤ dL n := by
  intro w hw
  rw [hrep w, hrep n]
  exact pairing_le_of_quad_le g hsymm hpsd n w hw

/-- Steepest descent: `-n` minimises `dL` on the same `g`-ball. -/
theorem steepest_descent (g : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (hsymm : ∀ u v, g u v = g v u)
    (hpsd : ∀ u, 0 ≤ g u u) (dL : V → ℝ) (n : V) (hrep : ∀ w, dL w = g n w) :
    ∀ w, g w w ≤ g n n → dL (-n) ≤ dL w := by
  intro w hw
  rw [hrep (-n), hrep w]
  simp only [map_neg]
  exact neg_quad_le_pairing g hsymm hpsd n w hw

end Abstract

/-! ### B. The explicit Fisher natural gradient on the simplex -/

section Fisher

variable {α : Type*} [Fintype α]

/-- The Fisher metric packaged as a real bilinear form on `α → ℝ`. -/
noncomputable def fisherBilin (P : ProbInterior α) : (α → ℝ) →ₗ[ℝ] (α → ℝ) →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fisherMetric P)
    (fun u₁ u₂ v => by
      simp only [fisherMetric, Pi.add_apply, add_mul, add_div, Finset.sum_add_distrib])
    (fun c u v => by
      simp only [fisherMetric, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc, mul_div_assoc])
    (fun u v₁ v₂ => by
      simp only [fisherMetric, Pi.add_apply, mul_add, add_div, Finset.sum_add_distrib])
    (fun c u v => by
      simp only [fisherMetric, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun a _ => by ring)

@[simp]
theorem fisherBilin_apply (P : ProbInterior α) (u v : α → ℝ) :
    fisherBilin P u v = fisherMetric P u v := rfl

/-- The `P`-expectation of a covector `ℓ`. -/
noncomputable def expectation (P : ProbInterior α) (ℓ : α → ℝ) : ℝ :=
  ∑ b, P.p b * ℓ b

/-- The Fisher natural gradient of the differential `w ↦ ∑ ℓ_a w_a` at `P`. -/
noncomputable def fisherNaturalGradient (P : ProbInterior α) (ℓ : α → ℝ) (a : α) : ℝ :=
  P.p a * (ℓ a - expectation P ℓ)

/-- The Fisher natural gradient is tangent to the simplex. -/
theorem fisherNaturalGradient_sum_zero (P : ProbInterior α) (ℓ : α → ℝ) :
    ∑ a, fisherNaturalGradient P ℓ a = 0 := by
  simp only [fisherNaturalGradient, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul,
    P.sum_one, one_mul, expectation, sub_self]

/-- The Fisher natural gradient represents the differential on tangent vectors. -/
theorem fisherMetric_naturalGradient (P : ProbInterior α) (ℓ : α → ℝ) (w : α → ℝ)
    (hw : ∑ a, w a = 0) :
    fisherMetric P (fisherNaturalGradient P ℓ) w = ∑ a, ℓ a * w a := by
  have hterm : ∀ a, fisherNaturalGradient P ℓ a * w a / P.p a =
      ℓ a * w a - expectation P ℓ * w a := by
    intro a
    have hp : P.p a ≠ 0 := (P.pos a).ne'
    unfold fisherNaturalGradient
    field_simp
  simp only [fisherMetric, hterm, Finset.sum_sub_distrib, ← Finset.mul_sum, hw, mul_zero, sub_zero]

/-- Uniqueness of the tangent Fisher representative of the differential. -/
theorem fisherNaturalGradient_unique (P : ProbInterior α) (ℓ n' : α → ℝ)
    (htan : ∑ a, n' a = 0)
    (hrep : ∀ w : α → ℝ, ∑ a, w a = 0 → fisherMetric P n' w = ∑ a, ℓ a * w a) :
    n' = fisherNaturalGradient P ℓ := by
  set n := fisherNaturalGradient P ℓ
  have hdtan : ∑ a, (n' - n) a = 0 := by
    simp only [Pi.sub_apply, Finset.sum_sub_distrib, htan, n, fisherNaturalGradient_sum_zero,
      sub_self]
  have hzero : fisherMetric P (n' - n) (n' - n) = 0 := by
    have h := map_sub (fisherBilin P) n' n
    have h' := congrArg (fun f => f (n' - n)) h
    simp only [LinearMap.sub_apply, fisherBilin_apply] at h'
    rw [h', hrep _ hdtan, fisherMetric_naturalGradient P ℓ _ hdtan, sub_self]
  exact sub_eq_zero.mp ((fisherMetric_eq_zero_iff P _).mp hzero)

/-- **Steepest ascent.** Among tangent directions of Fisher length at most that of the natural
gradient `n`, the first-order change `∑ ℓ_a w_a` is maximised at `n`. -/
theorem fisherNaturalGradient_steepest_ascent (P : ProbInterior α) (ℓ w : α → ℝ)
    (hw : ∑ a, w a = 0)
    (hlen : fisherMetric P w w ≤
      fisherMetric P (fisherNaturalGradient P ℓ) (fisherNaturalGradient P ℓ)) :
    ∑ a, ℓ a * w a ≤ ∑ a, ℓ a * fisherNaturalGradient P ℓ a := by
  rw [← fisherMetric_naturalGradient P ℓ w hw,
    ← fisherMetric_naturalGradient P ℓ _ (fisherNaturalGradient_sum_zero P ℓ)]
  exact pairing_le_of_quad_le (fisherBilin P) (fisherMetric_symm P) (fisherMetric_nonneg P)
    _ w hlen

/-- **Steepest descent.** The negative natural gradient minimises the first-order change on the
same tangent Fisher ball. -/
theorem fisherNaturalGradient_steepest_descent (P : ProbInterior α) (ℓ w : α → ℝ)
    (hw : ∑ a, w a = 0)
    (hlen : fisherMetric P w w ≤
      fisherMetric P (fisherNaturalGradient P ℓ) (fisherNaturalGradient P ℓ)) :
    ∑ a, ℓ a * (-fisherNaturalGradient P ℓ a) ≤ ∑ a, ℓ a * w a := by
  have h := neg_quad_le_pairing (fisherBilin P) (fisherMetric_symm P) (fisherMetric_nonneg P)
    _ w hlen
  simp only [fisherBilin_apply] at h
  rw [fisherMetric_naturalGradient P ℓ w hw,
    fisherMetric_naturalGradient P ℓ _ (fisherNaturalGradient_sum_zero P ℓ)] at h
  simpa only [mul_neg, Finset.sum_neg_distrib] using h

/-- The ascent rate equals the squared Fisher length of the natural gradient. -/
theorem fisherNaturalGradient_rate_eq_norm_sq (P : ProbInterior α) (ℓ : α → ℝ) :
    ∑ a, ℓ a * fisherNaturalGradient P ℓ a =
      fisherMetric P (fisherNaturalGradient P ℓ) (fisherNaturalGradient P ℓ) :=
  (fisherMetric_naturalGradient P ℓ _ (fisherNaturalGradient_sum_zero P ℓ)).symm

/-- The ascent rate equals the variance `Var_P ℓ = ∑ P_a ℓ_a² - (∑ P_a ℓ_a)²`. -/
theorem fisherNaturalGradient_rate_eq_variance (P : ProbInterior α) (ℓ : α → ℝ) :
    ∑ a, ℓ a * fisherNaturalGradient P ℓ a =
      ∑ a, P.p a * ℓ a ^ 2 - (∑ a, P.p a * ℓ a) ^ 2 := by
  have hterm : ∀ a, ℓ a * fisherNaturalGradient P ℓ a =
      P.p a * ℓ a ^ 2 - expectation P ℓ * (P.p a * ℓ a) := by
    intro a
    unfold fisherNaturalGradient
    ring
  simp only [hterm, Finset.sum_sub_distrib, ← Finset.mul_sum]
  unfold expectation
  ring

end Fisher

/-! ### C. Non-vacuity on `Bool` -/

/-- The uniform interior distribution on `Bool`. -/
noncomputable def uniformBool : ProbInterior Bool where
  p := fun _ => 1 / 2
  pos := fun _ => by norm_num
  sum_one := by norm_num [Fintype.sum_bool]

/-- The indicator covector of `true`. -/
def indicatorTrue (b : Bool) : ℝ := if b then 1 else 0

theorem uniformBool_naturalGradient_true :
    fisherNaturalGradient uniformBool indicatorTrue true = 1 / 4 := by
  norm_num [fisherNaturalGradient, expectation, uniformBool, indicatorTrue, Fintype.sum_bool]

/-- The natural gradient of a non-constant covector at the uniform point is nonzero. -/
theorem uniformBool_naturalGradient_ne_zero :
    fisherNaturalGradient uniformBool indicatorTrue ≠ 0 := by
  intro h
  have h1 := congrFun h true
  rw [uniformBool_naturalGradient_true] at h1
  norm_num at h1

/-- The variance (ascent rate) for the Bool example is `1/4`. -/
theorem uniformBool_rate :
    ∑ a, indicatorTrue a * fisherNaturalGradient uniformBool indicatorTrue a = 1 / 4 := by
  rw [fisherNaturalGradient_rate_eq_variance]
  norm_num [uniformBool, indicatorTrue, Fintype.sum_bool]

end InfoGeometry.Epistemology.FisherNaturalGradientSteepest
