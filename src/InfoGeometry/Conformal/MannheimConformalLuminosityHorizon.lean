/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Conformal.MannheimWeylKazanasCosmology
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.NhdsWithin
import Mathlib.Data.Matrix.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic

/-!
# Conformal Cosmology Luminosity Distance and Horizon-Free Growth

Formalizes the constructive conformal cosmology luminosity-distance and horizon-free growth
results from Philip Mannheim's conformal gravity lecture:

1. **Closed-form conformal luminosity distance** `d_L(z; H₀, q₀)`:
   `d_L(z) = -(c (1 + z)² / (H₀ q₀)) * (1 - √(1 + q₀ - q₀ / (1 + z)²))`
   with strict positivity of `conformalRadicand q₀ z` for `q₀ ∈ (-1, 0)` and `-1 < z`,
   vanishing at `z = 0`, and strict positivity for `z > 0` when `0 < c`, `0 < H₀`.
2. **Exact Taylor derivatives at `z = 0`**:
   `deriv d_L 0 = iteratedDeriv 1 d_L 0 = c / H₀` and
   `deriv (deriv d_L) 0 = iteratedDeriv 2 d_L 0 = (c / H₀) * (1 - q₀) > c / H₀` for `q₀ ∈ (-1, 0)`.
3. **Horizon-free conformal cosmology & growth ratios**:
   Exact FTC evaluation of the conformal particle horizon `∫ s in t_i..t, c / a(s)` and proof of
   divergence to `+∞` as `t_i → 0⁺`, contrasted with the uniformly bounded Einstein power-law
   horizon `∫ s in t_i..t, c * s ^ (-p)` for `0 < p < 1`, plus exact `sinh` monotonicity growth
   ratios and conformal vs. standard radiation-dominated nucleosynthesis and Planck-to-LS ratios.
4. **Friedmann instantiation**:
   Constructive instantiation of `H₀ := mannheimHubble S₀ lam k t` and
   `q₀ := mannheimDeceleration S₀ lam k t` via
   `mannheim_conformal_friedmann_ode_and_acceleration_constructive`.
-/

noncomputable section

namespace InfoGeometry.Conformal.MannheimConformalLuminosityHorizon

open Filter _root_.Topology
open Matrix BigOperators
open InfoGeometry.Conformal.MannheimWeylKazanasCosmology

/-! ## Non-Commutativity Witness on `M₂(ℝ)` (OpenGauss T16 Guardrail) -/

/-- Explicit `2 × 2` real matrix non-commutativity witness. -/
theorem conformal_luminosity_mat2_noncomm_witness :
    ∃ A B : Matrix (Fin 2) (Fin 2) ℝ, A * B ≠ B * A := by
  refine ⟨!![0, 1; 0, 0], !![0, 0; 1, 0], ?_⟩
  intro h
  have h00 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 0) h
  norm_num [Matrix.mul_apply, Fin.sum_univ_two] at h00

/-! ## Closed-Form Conformal Luminosity Distance & Exact Taylor Derivatives -/

/-- Radicand `1 + q₀ - q₀ / (1 + z)²` appearing in the conformal luminosity distance. -/
def conformalRadicand (q₀ z : ℝ) : ℝ :=
  1 + q₀ - q₀ / (1 + z) ^ 2

/-- Closed-form conformal cosmology luminosity distance
`d_L(z; H₀, q₀) = -(c (1 + z)² / (H₀ q₀)) (1 - √(1 + q₀ - q₀ / (1 + z)²))`. -/
def conformalLuminosityDist (c H₀ q₀ z : ℝ) : ℝ :=
  -(c * (1 + z) ^ 2 / (H₀ * q₀)) * (1 - Real.sqrt (conformalRadicand q₀ z))

/-- Closed-form first derivative `d_L'(z)` on `z > -1`. -/
def conformalLumDistDeriv1 (c H₀ q₀ z : ℝ) : ℝ :=
  -(2 * c * (1 + z) / (H₀ * q₀)) * (1 - Real.sqrt (conformalRadicand q₀ z)) +
    c / (H₀ * (1 + z) * Real.sqrt (conformalRadicand q₀ z))

/-- For `q₀ ∈ (-1, 0)` and `-1 < z`, `conformalRadicand q₀ z` is strictly positive. -/
theorem conformalRadicand_pos {q₀ z : ℝ} (hq : q₀ ∈ Set.Ioo (-1 : ℝ) 0) (hz : -1 < z) :
    0 < conformalRadicand q₀ z := by
  have hz1 : 0 < 1 + z := by linarith [hz]
  have hz2 : 0 < (1 + z) ^ 2 := sq_pos_of_pos hz1
  have h1q : 0 < 1 + q₀ := by linarith [hq.1]
  have hterm : 0 < -(q₀ / (1 + z) ^ 2) := by
    rw [← neg_div]
    exact div_pos (neg_pos.mpr hq.2) hz2
  unfold conformalRadicand
  linarith

/-- The conformal luminosity distance vanishes at redshift `z = 0`. -/
theorem conformalLuminosityDist_zero (c H₀ q₀ : ℝ) :
    conformalLuminosityDist c H₀ q₀ 0 = 0 := by
  have hr0 : conformalRadicand q₀ 0 = 1 := by
    unfold conformalRadicand
    ring
  unfold conformalLuminosityDist
  rw [hr0, Real.sqrt_one]
  ring

/-- For `0 < c`, `0 < H₀`, `q₀ ∈ (-1, 0)`, and `0 < z`, `conformalLuminosityDist c H₀ q₀ z > 0`. -/
theorem conformalLuminosityDist_pos {c H₀ q₀ z : ℝ}
    (hc : 0 < c) (hH : 0 < H₀) (hq : q₀ ∈ Set.Ioo (-1 : ℝ) 0) (hz : 0 < z) :
    0 < conformalLuminosityDist c H₀ q₀ z := by
  have hz1 : 0 < 1 + z := by linarith [hz]
  have hz2 : 0 < (1 + z) ^ 2 := sq_pos_of_pos hz1
  have hz2_gt1 : 1 < (1 + z) ^ 2 := by nlinarith
  have hpref_neg : c * (1 + z) ^ 2 / (H₀ * q₀) < 0 :=
    div_neg_of_pos_of_neg (mul_pos hc hz2) (mul_neg_of_pos_of_neg hH hq.2)
  have hpref_pos : 0 < -(c * (1 + z) ^ 2 / (H₀ * q₀)) := neg_pos.mpr hpref_neg
  have hfrac_lt : -(q₀ / (1 + z) ^ 2) < -q₀ := by
    rw [← neg_div, div_lt_iff₀ hz2]
    nlinarith [hq.2, hz2_gt1]
  have hrad_lt : conformalRadicand q₀ z < 1 := by
    unfold conformalRadicand
    linarith
  have hsqrt_lt : Real.sqrt (conformalRadicand q₀ z) < 1 :=
    (Real.sqrt_lt' zero_lt_one).mpr (by norm_num; exact hrad_lt)
  exact mul_pos hpref_pos (sub_pos.mpr hsqrt_lt)

/-- Derivative of `conformalRadicand q₀` at any `z > -1`. -/
lemma has_deriv_at_conformal_radicand (q₀ : ℝ) {z : ℝ} (hz : -1 < z) :
    HasDerivAt (conformalRadicand q₀) (2 * q₀ / (1 + z) ^ 3) z := by
  have hz1 : 0 < 1 + z := by linarith [hz]
  have hsq_ne : (1 + z) ^ 2 ≠ 0 := pow_ne_zero 2 hz1.ne'
  have h1z : HasDerivAt (fun x : ℝ => 1 + x) 1 z := (hasDerivAt_id' z).const_add 1
  have hsq : HasDerivAt (fun x : ℝ => (1 + x) ^ 2) (2 * (1 + z)) z :=
    (h1z.fun_pow 2).congr_deriv (by simp)
  have hdiv : HasDerivAt (fun x : ℝ => q₀ / (1 + x) ^ 2) (-(2 * q₀ / (1 + z) ^ 3)) z := by
    refine ((hasDerivAt_const z q₀).fun_div hsq hsq_ne).congr_deriv ?_
    field_simp [hz1.ne']
    ring
  have hsub : HasDerivAt (conformalRadicand q₀) (0 - -(2 * q₀ / (1 + z) ^ 3)) z :=
    (hasDerivAt_const z (1 + q₀)).fun_sub hdiv
  exact hsub.congr_deriv (by ring)

/-- `HasDerivAt` formula for `conformalLuminosityDist c H₀ q₀` at any `z > -1`. -/
lemma has_deriv_at_conformal_luminosity_dist {c H₀ q₀ z : ℝ}
    (hH : H₀ ≠ 0) (hq : q₀ ∈ Set.Ioo (-1 : ℝ) 0) (hz : -1 < z) :
    HasDerivAt (conformalLuminosityDist c H₀ q₀) (conformalLumDistDeriv1 c H₀ q₀ z) z := by
  have hz1 : 0 < 1 + z := by linarith
  have hr_pos : 0 < conformalRadicand q₀ z := conformalRadicand_pos hq hz
  have hsqrt_pos : 0 < Real.sqrt (conformalRadicand q₀ z) := Real.sqrt_pos.mpr hr_pos
  have h1z : HasDerivAt (fun x : ℝ => 1 + x) 1 z := (hasDerivAt_id' z).const_add 1
  have hsq : HasDerivAt (fun x : ℝ => (1 + x) ^ 2) (2 * (1 + z)) z :=
    (h1z.fun_pow 2).congr_deriv (by simp)
  have hpref : HasDerivAt (fun x : ℝ => -(c * (1 + x) ^ 2 / (H₀ * q₀)))
      (-(2 * c * (1 + z) / (H₀ * q₀))) z := by
    refine (((hsq.const_mul c).div_const (H₀ * q₀)).fun_neg).congr_deriv ?_
    ring
  have hr := has_deriv_at_conformal_radicand q₀ hz
  have hsqrt := hr.sqrt hr_pos.ne'
  have hfac : HasDerivAt (fun x : ℝ => 1 - Real.sqrt (conformalRadicand q₀ x))
      (-(q₀ / ((1 + z) ^ 3 * Real.sqrt (conformalRadicand q₀ z)))) z := by
    refine (hsqrt.const_sub 1).congr_deriv ?_
    field_simp [hz1.ne', hsqrt_pos.ne']
  refine (hpref.fun_mul hfac).congr_deriv ?_
  unfold conformalLumDistDeriv1
  field_simp [hH, hq.2.ne, hz1.ne', hsqrt_pos.ne']

/-- Pointwise equality `deriv (conformalLuminosityDist c H₀ q₀) z = conformalLumDistDeriv1 ...`
for `z > -1`. -/
theorem conformal_luminosity_dist_deriv1_eq {c H₀ q₀ z : ℝ}
    (hH : H₀ ≠ 0) (hq : q₀ ∈ Set.Ioo (-1 : ℝ) 0) (hz : -1 < z) :
    deriv (conformalLuminosityDist c H₀ q₀) z = conformalLumDistDeriv1 c H₀ q₀ z :=
  (has_deriv_at_conformal_luminosity_dist hH hq hz).deriv

/-- Exact first Taylor derivative at `z = 0`: `d_L'(0) = c / H₀` (both `deriv` and
`iteratedDeriv 1`). -/
theorem conformalLuminosityDist_deriv1_zero {c H₀ q₀ : ℝ}
    (hH : H₀ ≠ 0) (hq : q₀ ∈ Set.Ioo (-1 : ℝ) 0) :
    deriv (conformalLuminosityDist c H₀ q₀) 0 = c / H₀ ∧
    iteratedDeriv 1 (conformalLuminosityDist c H₀ q₀) 0 = c / H₀ := by
  have hd1 : deriv (conformalLuminosityDist c H₀ q₀) 0 = c / H₀ := by
    rw [conformal_luminosity_dist_deriv1_eq hH hq (by norm_num : (-1 : ℝ) < 0)]
    simp [conformalLumDistDeriv1, conformalRadicand]
  refine ⟨hd1, ?_⟩
  rw [iteratedDeriv_one]
  exact hd1

/-- Exact second Taylor derivative at `z = 0`: `d_L''(0) = (c / H₀) * (1 - q₀) > c / H₀` for
`0 < c`, `0 < H₀`, and `q₀ ∈ (-1, 0)` (both `deriv (deriv ...)` and `iteratedDeriv 2`). -/
theorem conformalLuminosityDist_deriv2_zero {c H₀ q₀ : ℝ}
    (hc : 0 < c) (hH : 0 < H₀) (hq : q₀ ∈ Set.Ioo (-1 : ℝ) 0) :
    deriv (deriv (conformalLuminosityDist c H₀ q₀)) 0 = (c / H₀) * (1 - q₀) ∧
    iteratedDeriv 2 (conformalLuminosityDist c H₀ q₀) 0 = (c / H₀) * (1 - q₀) ∧
    c / H₀ < (c / H₀) * (1 - q₀) := by
  have hev : deriv (conformalLuminosityDist c H₀ q₀) =ᶠ[𝓝 0] conformalLumDistDeriv1 c H₀ q₀ := by
    filter_upwards [isOpen_Ioi.mem_nhds (by norm_num : (-1 : ℝ) < 0)] with z hz
    exact conformal_luminosity_dist_deriv1_eq hH.ne' hq hz
  have hr0 : conformalRadicand q₀ 0 = 1 := by simp [conformalRadicand]
  have hr0_sqrt : Real.sqrt (conformalRadicand q₀ 0) = 1 := by rw [hr0, Real.sqrt_one]
  have h1z : HasDerivAt (fun x : ℝ => 1 + x) 1 0 := (hasDerivAt_id' 0).const_add 1
  have hr : HasDerivAt (conformalRadicand q₀) (2 * q₀) 0 :=
    (has_deriv_at_conformal_radicand q₀ (by norm_num : (-1 : ℝ) < 0)).congr_deriv (by norm_num)
  have hsqrt : HasDerivAt (fun x : ℝ => Real.sqrt (conformalRadicand q₀ x)) q₀ 0 := by
    refine (hr.sqrt (by rw [hr0]; exact one_ne_zero)).congr_deriv ?_
    rw [hr0_sqrt]
    ring
  have hfac : HasDerivAt (fun x : ℝ => 1 - Real.sqrt (conformalRadicand q₀ x)) (-q₀) 0 :=
    hsqrt.const_sub 1
  have hT1_left : HasDerivAt (fun x : ℝ => -(2 * c * (1 + x) / (H₀ * q₀)))
      (-(2 * c / (H₀ * q₀))) 0 := by
    refine (((h1z.const_mul (2 * c)).div_const (H₀ * q₀)).fun_neg).congr_deriv ?_
    ring
  have hT1 : HasDerivAt
      (fun x : ℝ =>
        -(2 * c * (1 + x) / (H₀ * q₀)) * (1 - Real.sqrt (conformalRadicand q₀ x)))
      (2 * c / H₀) 0 := by
    refine (hT1_left.fun_mul hfac).congr_deriv ?_
    rw [hr0_sqrt]
    field_simp [hH.ne', hq.2.ne]
    ring
  have hg : HasDerivAt (fun x : ℝ => H₀ * (1 + x) * Real.sqrt (conformalRadicand q₀ x))
      (H₀ * (1 + q₀)) 0 := by
    refine ((h1z.const_mul H₀).fun_mul hsqrt).congr_deriv ?_
    rw [hr0_sqrt]
    ring
  have hg0_ne : H₀ * (1 + (0 : ℝ)) * Real.sqrt (conformalRadicand q₀ 0) ≠ 0 := by
    rw [hr0_sqrt]
    simpa using hH.ne'
  have hT2 : HasDerivAt (fun x : ℝ => c / (H₀ * (1 + x) * Real.sqrt (conformalRadicand q₀ x)))
      (-(c / H₀) * (1 + q₀)) 0 := by
    refine ((hasDerivAt_const 0 c).fun_div hg hg0_ne).congr_deriv ?_
    rw [hr0_sqrt]
    field_simp [hH.ne']
    ring
  have htot : HasDerivAt (conformalLumDistDeriv1 c H₀ q₀) ((c / H₀) * (1 - q₀)) 0 :=
    (hT1.fun_add hT2).congr_deriv (by ring)
  have hd2 : deriv (deriv (conformalLuminosityDist c H₀ q₀)) 0 = (c / H₀) * (1 - q₀) := by
    rw [hev.deriv_eq]
    exact htot.deriv
  have hi2 : iteratedDeriv 2 (conformalLuminosityDist c H₀ q₀) 0 = (c / H₀) * (1 - q₀) := by
    rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]
    exact hd2
  have hgt : c / H₀ < (c / H₀) * (1 - q₀) :=
    lt_mul_of_one_lt_right (div_pos hc hH) (by linarith [hq.2])
  exact ⟨hd2, hi2, hgt⟩

/-! ## Horizon-Free Conformal Cosmology & Growth Ratios -/

/-- Comoving conformal particle horizon `∫ s in t_i..t, c / a(s)` for the open conformal
scale factor `mannheimScaleFactor S₀ lam k`. -/
def conformalHorizon (c S₀ lam k t_i t : ℝ) : ℝ :=
  ∫ s in t_i..t, c / mannheimScaleFactor S₀ lam k s

/-- Comoving particle horizon `∫ s in t_i..t, c * s ^ (-p)` in an Einstein power-law cosmology
`a(t) ∝ t ^ p` (`0 < p < 1`). -/
def einsteinPowerHorizon (c p t_i t : ℝ) : ℝ :=
  ∫ s in t_i..t, c * s ^ (-p)

/-- Helper antiderivative `F(s) = (c / √(-k)) * (log (sinh (μ s / 2)) - log (cosh (μ s / 2)))`
for `c / mannheimScaleFactor S₀ lam k s` on `s > 0`. -/
lemma conformal_horizon_antideriv_has_deriv_at
    {c S₀ lam k s : ℝ} (hS : S₀ ≠ 0) (hlam : 0 < lam) (hk : k < 0) (hs : 0 < s) :
    let μ := mannheimCosmoRate S₀ lam
    HasDerivAt
      (fun x : ℝ => (c / Real.sqrt (-k)) *
        (Real.log (Real.sinh (μ * x / 2)) - Real.log (Real.cosh (μ * x / 2))))
      (c / mannheimScaleFactor S₀ lam k s) s := by
  intro μ
  have hμ2_pos : 0 < 2 * lam * S₀ ^ 2 :=
    mul_pos (mul_pos zero_lt_two hlam) (sq_pos_of_ne_zero hS)
  have hμ_pos : 0 < μ := Real.sqrt_pos.mpr hμ2_pos
  have hrk_pos : 0 < Real.sqrt (-k) := Real.sqrt_pos.mpr (neg_pos.mpr hk)
  have harg_pos : 0 < μ * s / 2 := div_pos (mul_pos hμ_pos hs) zero_lt_two
  have hsinh_pos : 0 < Real.sinh (μ * s / 2) := Real.sinh_pos_iff.mpr harg_pos
  have hcosh_pos : 0 < Real.cosh (μ * s / 2) := Real.cosh_pos _
  have hu : HasDerivAt (fun x : ℝ => μ * x / 2) (μ / 2) s := by
    simpa using ((hasDerivAt_id s).const_mul μ).div_const 2
  have hls : HasDerivAt (fun x : ℝ => Real.log (Real.sinh (μ * x / 2)))
      (Real.cosh (μ * s / 2) * (μ / 2) / Real.sinh (μ * s / 2)) s :=
    hu.sinh.log hsinh_pos.ne'
  have hlc : HasDerivAt (fun x : ℝ => Real.log (Real.cosh (μ * x / 2)))
      (Real.sinh (μ * s / 2) * (μ / 2) / Real.cosh (μ * s / 2)) s :=
    hu.cosh.log hcosh_pos.ne'
  refine ((hls.sub hlc).const_mul (c / Real.sqrt (-k))).congr_deriv ?_
  have hsinh_full : Real.sinh (μ * s) =
      2 * Real.sinh (μ * s / 2) * Real.cosh (μ * s / 2) := by
    simpa [show 2 * (μ * s / 2) = μ * s by ring] using Real.sinh_two_mul (μ * s / 2)
  have hcosh_sinh : Real.cosh (μ * s / 2) ^ 2 - Real.sinh (μ * s / 2) ^ 2 = 1 :=
    Real.cosh_sq_sub_sinh_sq (μ * s / 2)
  have hscale : mannheimScaleFactor S₀ lam k s =
      (Real.sqrt (-k) / μ) * (2 * Real.sinh (μ * s / 2) * Real.cosh (μ * s / 2)) := by
    dsimp only [mannheimScaleFactor]
    rw [show mannheimCosmoRate S₀ lam = μ by rfl, hsinh_full]
  rw [hscale]
  field_simp [hrk_pos.ne', hμ_pos.ne', hsinh_pos.ne', hcosh_pos.ne']
  calc
    c * (Real.cosh (μ * s / 2) ^ 2 - Real.sinh (μ * s / 2) ^ 2)
        = c * 1 := by rw [hcosh_sinh]
    _ = c := by ring

/-- Exact closed-form evaluation of `conformalHorizon c S₀ lam k t_i t` for `0 < t_i` and
`0 < t` via the Fundamental Theorem of Calculus. -/
lemma conformal_horizon_eq_of_pos
    (c : ℝ) {S₀ lam k t_i t : ℝ} (hS : S₀ ≠ 0) (hlam : 0 < lam)
    (hk : k < 0) (ht_i : 0 < t_i) (ht : 0 < t) :
    conformalHorizon c S₀ lam k t_i t =
      (c / Real.sqrt (-k)) *
        (Real.log (Real.tanh (mannheimCosmoRate S₀ lam * t / 2)) -
         Real.log (Real.tanh (mannheimCosmoRate S₀ lam * t_i / 2))) := by
  let μ := mannheimCosmoRate S₀ lam
  have hμ2_pos : 0 < 2 * lam * S₀ ^ 2 :=
    mul_pos (mul_pos zero_lt_two hlam) (sq_pos_of_ne_zero hS)
  have hμ_pos : 0 < μ := Real.sqrt_pos.mpr hμ2_pos
  have hrk_pos : 0 < Real.sqrt (-k) := Real.sqrt_pos.mpr (neg_pos.mpr hk)
  let F : ℝ → ℝ := fun x =>
    (c / Real.sqrt (-k)) * (Real.log (Real.sinh (μ * x / 2)) - Real.log (Real.cosh (μ * x / 2)))
  have hderiv : ∀ x ∈ Set.uIcc t_i t, HasDerivAt F (c / mannheimScaleFactor S₀ lam k x) x := by
    intro x hx
    have hx_pos : 0 < x := lt_of_lt_of_le (lt_min ht_i ht) hx.1
    exact conformal_horizon_antideriv_has_deriv_at hS hlam hk hx_pos
  have hcont_den : ContinuousOn (fun x => mannheimScaleFactor S₀ lam k x) (Set.uIcc t_i t) := by
    refine Continuous.continuousOn ?_
    unfold mannheimScaleFactor
    exact continuous_const.mul (Real.continuous_sinh.comp (continuous_const.mul continuous_id))
  have hne_den : ∀ x ∈ Set.uIcc t_i t, mannheimScaleFactor S₀ lam k x ≠ 0 := by
    intro x hx
    have hx_pos : 0 < x := lt_of_lt_of_le (lt_min ht_i ht) hx.1
    have hsinh_pos : 0 < Real.sinh (μ * x) := Real.sinh_pos_iff.mpr (mul_pos hμ_pos hx_pos)
    unfold mannheimScaleFactor
    exact mul_ne_zero (div_ne_zero hrk_pos.ne' hμ_pos.ne') hsinh_pos.ne'
  have hint : IntervalIntegrable (fun x => c / mannheimScaleFactor S₀ lam k x)
      MeasureTheory.volume t_i t :=
    (continuousOn_const.div hcont_den hne_den).intervalIntegrable
  have hftc : conformalHorizon c S₀ lam k t_i t = F t - F t_i := by
    unfold conformalHorizon
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  have hlog_tanh : ∀ x : ℝ, 0 < x →
      Real.log (Real.sinh (μ * x / 2)) - Real.log (Real.cosh (μ * x / 2)) =
        Real.log (Real.tanh (μ * x / 2)) := by
    intro x hx
    have hs_ne : Real.sinh (μ * x / 2) ≠ 0 :=
      (Real.sinh_pos_iff.mpr (by positivity)).ne'
    have hc_ne : Real.cosh (μ * x / 2) ≠ 0 := (Real.cosh_pos _).ne'
    rw [← Real.log_div hs_ne hc_ne, ← Real.tanh_eq_sinh_div_cosh]
  rw [hftc]
  dsimp only [F]
  rw [← hlog_tanh t ht, ← hlog_tanh t_i ht_i]
  ring

/-- **Horizon-Free Conformal Cosmology Theorem**:
1. Closed-form FTC evaluation of `conformalHorizon c S₀ lam k t_i t` in terms of `log (tanh (μ s / 2))`;
2. As `t_i → 0⁺`, `conformalHorizon c S₀ lam k t_i t → +∞` (`Filter.atTop`), eliminating the
   cosmological horizon problem without inflation. -/
theorem conformalHorizon_eq_and_tendsto_atTop
    {c S₀ lam k t : ℝ} (hc : 0 < c) (hS : S₀ ≠ 0) (hlam : 0 < lam)
    (hk : k < 0) (ht : 0 < t) :
    (∀ t_i : ℝ, 0 < t_i →
      conformalHorizon c S₀ lam k t_i t =
        (c / Real.sqrt (-k)) *
          (Real.log (Real.tanh (mannheimCosmoRate S₀ lam * t / 2)) -
           Real.log (Real.tanh (mannheimCosmoRate S₀ lam * t_i / 2)))) ∧
    Tendsto (fun t_i => conformalHorizon c S₀ lam k t_i t) (𝓝[>] 0) Filter.atTop := by
  refine ⟨fun t_i hti => conformal_horizon_eq_of_pos c hS hlam hk hti ht, ?_⟩
  let μ := mannheimCosmoRate S₀ lam
  have hμ2_pos : 0 < 2 * lam * S₀ ^ 2 :=
    mul_pos (mul_pos zero_lt_two hlam) (sq_pos_of_ne_zero hS)
  have hμ_pos : 0 < μ := Real.sqrt_pos.mpr hμ2_pos
  have hrk_pos : 0 < Real.sqrt (-k) := Real.sqrt_pos.mpr (neg_pos.mpr hk)
  have hfac_pos : 0 < c / Real.sqrt (-k) := div_pos hc hrk_pos
  have hsinh_tendsto :
      Tendsto (fun t_i : ℝ => Real.sinh (μ * t_i / 2)) (𝓝[>] 0) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have hcont : Continuous (fun t_i : ℝ => Real.sinh (μ * t_i / 2)) :=
        Real.continuous_sinh.comp ((continuous_const.mul continuous_id).div_const 2)
      have h0 := (hcont.continuousAt (x := 0)).tendsto
      simp only [mul_zero, zero_div, Real.sinh_zero] at h0
      exact h0.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with x (hx : 0 < x)
      exact Real.sinh_pos_iff.mpr (by positivity)
  have hlog_bot :
      Tendsto (fun t_i : ℝ => Real.log (Real.sinh (μ * t_i / 2))) (𝓝[>] 0) Filter.atBot :=
    Real.tendsto_log_nhdsGT_zero.comp hsinh_tendsto
  have hneg_top :
      Tendsto (fun t_i : ℝ => -Real.log (Real.sinh (μ * t_i / 2))) (𝓝[>] 0) Filter.atTop :=
    Filter.tendsto_neg_atBot_atTop.comp hlog_bot
  have hsum_top :
      Tendsto (fun t_i : ℝ =>
        Real.log (Real.cosh (μ * t_i / 2)) + -Real.log (Real.sinh (μ * t_i / 2)))
        (𝓝[>] 0) Filter.atTop :=
    Filter.tendsto_atTop_add_left_of_le (𝓝[>] 0) 0
      (fun x => Real.log_nonneg (Real.one_le_cosh (μ * x / 2))) hneg_top
  have hscaled_top := hsum_top.const_mul_atTop hfac_pos
  let C : ℝ := (c / Real.sqrt (-k)) * Real.log (Real.tanh (μ * t / 2))
  have hshifted_top :
      Tendsto (fun t_i : ℝ =>
        C + (c / Real.sqrt (-k)) *
          (Real.log (Real.cosh (μ * t_i / 2)) + -Real.log (Real.sinh (μ * t_i / 2))))
        (𝓝[>] 0) Filter.atTop :=
    Filter.tendsto_atTop_add_const_left (𝓝[>] 0) C hscaled_top
  refine hshifted_top.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t_i (hti : 0 < t_i)
  rw [conformal_horizon_eq_of_pos c hS hlam hk hti ht]
  have hs_ne : Real.sinh (μ * t_i / 2) ≠ 0 :=
    (Real.sinh_pos_iff.mpr (by positivity)).ne'
  have hc_ne : Real.cosh (μ * t_i / 2) ≠ 0 := (Real.cosh_pos _).ne'
  have hlt : Real.log (Real.tanh (μ * t_i / 2)) =
      Real.log (Real.sinh (μ * t_i / 2)) - Real.log (Real.cosh (μ * t_i / 2)) := by
    rw [Real.tanh_eq_sinh_div_cosh, Real.log_div hs_ne hc_ne]
  rw [hlt]
  dsimp only [C, μ]
  ring

/-- **Uniform Boundedness of Einstein Power-Law Horizon**:
For `a(t) ∝ t ^ p` with `0 < p < 1` (covering radiation `p = 1/2` and matter `p = 2/3`),
`einsteinPowerHorizon c p t_i t` evaluates exactly to `c * (t ^ (1 - p) - t_i ^ (1 - p)) / (1 - p)`,
remains nonnegative for `0 ≤ t_i ≤ t` (`0 ≤ c`), and is uniformly bounded above by
`c * t ^ (1 - p) / (1 - p)` independent of `t_i`. -/
theorem einsteinPowerHorizon_bounded
    {c p t_i t : ℝ} (hc : 0 ≤ c) (hp0 : 0 < p) (hp1 : p < 1)
    (ht_i : 0 ≤ t_i) (hle : t_i ≤ t) :
    einsteinPowerHorizon c p t_i t = c * (t ^ (1 - p) - t_i ^ (1 - p)) / (1 - p) ∧
    0 ≤ einsteinPowerHorizon c p t_i t ∧
    einsteinPowerHorizon c p t_i t ≤ c * t ^ (1 - p) / (1 - p) ∧
    1 - p < 1 := by
  have hp_sub_pos : 0 < 1 - p := sub_pos.mpr hp1
  have heval :
      einsteinPowerHorizon c p t_i t = c * (t ^ (1 - p) - t_i ^ (1 - p)) / (1 - p) := by
    unfold einsteinPowerHorizon
    rw [intervalIntegral.integral_const_mul, integral_rpow (Or.inl (by linarith))]
    rw [show -p + 1 = 1 - p by ring]
    ring
  have hrpow_nonneg : 0 ≤ t_i ^ (1 - p) := Real.rpow_nonneg ht_i (1 - p)
  have hrpow_le : t_i ^ (1 - p) ≤ t ^ (1 - p) :=
    Real.rpow_le_rpow ht_i hle hp_sub_pos.le
  have hnonneg : 0 ≤ einsteinPowerHorizon c p t_i t := by
    rw [heval]
    exact div_nonneg (mul_nonneg hc (sub_nonneg.mpr hrpow_le)) hp_sub_pos.le
  have hupper : einsteinPowerHorizon c p t_i t ≤ c * t ^ (1 - p) / (1 - p) := by
    rw [heval]
    refine div_le_div_of_nonneg_right ?_ hp_sub_pos.le
    exact mul_le_mul_of_nonneg_left (sub_le_self _ hrpow_nonneg) hc
  exact ⟨heval, hnonneg, hupper, sub_lt_self 1 hp0⟩

/-- For all `x > 0`, `Real.sinh x < x * Real.cosh x`. -/
lemma sinh_lt_mul_cosh_of_pos {x : ℝ} (hx : 0 < x) :
    Real.sinh x < x * Real.cosh x := by
  let f : ℝ → ℝ := fun y => y * Real.cosh y - Real.sinh y
  have hcont : Continuous f := (continuous_id.mul Real.continuous_cosh).sub Real.continuous_sinh
  have hderiv : ∀ y : ℝ, HasDerivAt f (y * Real.sinh y) y := by
    intro y
    refine (((hasDerivAt_id y).mul (Real.hasDerivAt_cosh y)).sub
      (Real.hasDerivAt_sinh y)).congr_deriv ?_
    simp only [id_eq, one_mul]
    ring
  have hpos_deriv : ∀ y ∈ interior (Set.Ici (0 : ℝ)), 0 < deriv f y := by
    intro y hy
    rw [interior_Ici] at hy
    rw [(hderiv y).deriv]
    exact mul_pos hy (Real.sinh_pos_iff.mpr hy)
  have hmono : StrictMonoOn f (Set.Ici (0 : ℝ)) :=
    strictMonoOn_of_deriv_pos (convex_Ici (0 : ℝ)) hcont.continuousOn hpos_deriv
  have hlt := hmono (Set.mem_Ici.mpr (le_refl 0)) (le_of_lt hx) hx
  dsimp only [f] at hlt
  simp only [zero_mul, Real.sinh_zero, sub_zero] at hlt
  linarith

/-- On `Set.Ioi 0`, `x ↦ Real.sinh x / x` is strictly monotone increasing. -/
lemma sinh_div_strict_mono_on_ioi :
    StrictMonoOn (fun x : ℝ => Real.sinh x / x) (Set.Ioi 0) := by
  have hcont : ContinuousOn (fun x : ℝ => Real.sinh x / x) (Set.Ioi 0) :=
    Real.continuous_sinh.continuousOn.div continuousOn_id (fun _ hx => hx.ne')
  have hpos_deriv : ∀ x ∈ interior (Set.Ioi (0 : ℝ)),
      0 < deriv (fun y : ℝ => Real.sinh y / y) x := by
    intro x hx
    rw [isOpen_Ioi.interior_eq] at hx
    have hdx : HasDerivAt (fun y : ℝ => Real.sinh y / y)
        ((Real.cosh x * x - Real.sinh x * 1) / x ^ 2) x :=
      (Real.hasDerivAt_sinh x).div (hasDerivAt_id x) hx.ne'
    rw [hdx.deriv]
    refine div_pos ?_ (sq_pos_of_pos hx)
    linarith [sinh_lt_mul_cosh_of_pos hx]
  exact strictMonoOn_of_deriv_pos (convex_Ioi (0 : ℝ)) hcont hpos_deriv

/-- **Conformal vs. Standard Nucleosynthesis and Planck-to-Last-Scattering Growth/Time Ratios**:
1. Exact `sinh` scale-factor monotonicity ratio:
   `t₂ / t₁ < mannheimScaleFactor S₀ lam k t₂ / mannheimScaleFactor S₀ lam k t₁` for
   `S₀ ≠ 0`, `0 < lam`, `k < 0`, `0 < t₁ < t₂`;
2. Strict outpacing over standard radiation-dominated `t^(1/2)` growth:
   `(t₂ / t₁) ^ (1 / 2 : ℝ) < t₂ / t₁`;
3. For any temperature ratio `R = T₁ / T₂ > 1` (e.g., `T_Pl / T_ls` or nucleosynthesis ratio):
   `1 < R` and `R < R ^ 2`, conformal expansion matching `a(t₂) / a(t₁) = R` requires strictly
   less time ratio `t₂ / t₁ < R < R ^ 2`, whereas standard radiation-dominated scaling
   `r_std ^ (1 / 2 : ℝ) = R` forces `r_std = R ^ 2`. -/
theorem conformal_vs_standard_nucleosynthesis_and_planck_ratios
    {S₀ lam k t₁ t₂ T₁ T₂ : ℝ}
    (hS : S₀ ≠ 0) (hlam : 0 < lam) (hk : k < 0)
    (ht₁ : 0 < t₁) (ht₁₂ : t₁ < t₂)
    (hT₂ : 0 < T₂) (hT₁₂ : T₂ < T₁) :
    t₂ / t₁ < mannheimScaleFactor S₀ lam k t₂ / mannheimScaleFactor S₀ lam k t₁ ∧
    (t₂ / t₁) ^ (1 / 2 : ℝ) < t₂ / t₁ ∧
    1 < T₁ / T₂ ∧
    T₁ / T₂ < (T₁ / T₂) ^ 2 ∧
    (mannheimScaleFactor S₀ lam k t₂ / mannheimScaleFactor S₀ lam k t₁ = T₁ / T₂ →
      t₂ / t₁ < T₁ / T₂ ∧ t₂ / t₁ < (T₁ / T₂) ^ 2) ∧
    (∀ r_std : ℝ, 0 ≤ r_std → r_std ^ (1 / 2 : ℝ) = T₁ / T₂ → r_std = (T₁ / T₂) ^ 2) := by
  let μ := mannheimCosmoRate S₀ lam
  have hμ2_pos : 0 < 2 * lam * S₀ ^ 2 :=
    mul_pos (mul_pos zero_lt_two hlam) (sq_pos_of_ne_zero hS)
  have hμ_pos : 0 < μ := Real.sqrt_pos.mpr hμ2_pos
  have hrk_pos : 0 < Real.sqrt (-k) := Real.sqrt_pos.mpr (neg_pos.mpr hk)
  have ht₂ : 0 < t₂ := lt_trans ht₁ ht₁₂
  have hμt₁ : 0 < μ * t₁ := mul_pos hμ_pos ht₁
  have hμt₂ : 0 < μ * t₂ := mul_pos hμ_pos ht₂
  have hμt₁₂ : μ * t₁ < μ * t₂ := mul_lt_mul_of_pos_left ht₁₂ hμ_pos
  have hmono : Real.sinh (μ * t₁) / (μ * t₁) < Real.sinh (μ * t₂) / (μ * t₂) :=
    sinh_div_strict_mono_on_ioi hμt₁ hμt₂ hμt₁₂
  have hsinh₁_pos : 0 < Real.sinh (μ * t₁) := Real.sinh_pos_iff.mpr hμt₁
  have hratio_sinh : t₂ / t₁ < Real.sinh (μ * t₂) / Real.sinh (μ * t₁) := by
    rw [div_lt_div_iff₀ ht₁ hsinh₁_pos]
    rw [div_lt_div_iff₀ hμt₁ hμt₂] at hmono
    have hcancel : μ * (t₂ * Real.sinh (μ * t₁)) < μ * (Real.sinh (μ * t₂) * t₁) := by
      linarith
    exact lt_of_mul_lt_mul_left hcancel hμ_pos.le
  have hscale_ratio_eq :
      mannheimScaleFactor S₀ lam k t₂ / mannheimScaleFactor S₀ lam k t₁ =
        Real.sinh (μ * t₂) / Real.sinh (μ * t₁) := by
    unfold mannheimScaleFactor
    change (Real.sqrt (-k) / μ * Real.sinh (μ * t₂)) /
        (Real.sqrt (-k) / μ * Real.sinh (μ * t₁)) = _
    have hpref_ne : Real.sqrt (-k) / μ ≠ 0 := div_ne_zero hrk_pos.ne' hμ_pos.ne'
    field_simp [hpref_ne, hsinh₁_pos.ne']
  have hscale_gt :
      t₂ / t₁ < mannheimScaleFactor S₀ lam k t₂ / mannheimScaleFactor S₀ lam k t₁ := by
    rw [hscale_ratio_eq]
    exact hratio_sinh
  have hr_gt1 : 1 < T₁ / T₂ := (one_lt_div hT₂).mpr hT₁₂
  have hr_lt_sq : T₁ / T₂ < (T₁ / T₂) ^ 2 := by nlinarith
  have htime_gt1 : 1 < t₂ / t₁ := (one_lt_div ht₁).mpr ht₁₂
  have htime_sqrt_lt : (t₂ / t₁) ^ (1 / 2 : ℝ) < t₂ / t₁ := by
    rw [← Real.sqrt_eq_rpow]
    rw [Real.sqrt_lt' (by linarith)]
    nlinarith
  refine ⟨hscale_gt, htime_sqrt_lt, hr_gt1, hr_lt_sq, ?_, ?_⟩
  · intro heq
    have hlt1 : t₂ / t₁ < T₁ / T₂ := by rwa [← heq]
    exact ⟨hlt1, lt_trans hlt1 hr_lt_sq⟩
  · intro r_std hr_nonneg hr_eq
    have hrpow : (r_std ^ (1 / 2 : ℝ)) ^ 2 = (T₁ / T₂) ^ 2 := congrArg (fun x => x ^ 2) hr_eq
    rw [← Real.rpow_natCast, ← Real.rpow_mul hr_nonneg] at hrpow
    norm_num at hrpow
    exact hrpow

/-! ## Constructive Friedmann Instantiation -/

/-- **Friedmann Instantiation of Conformal Luminosity Distance and Horizon Divergence**:
Instantiates `H₀ := mannheimHubble S₀ lam k t` and `q₀ := mannheimDeceleration S₀ lam k t`
directly from `mannheim_conformal_friedmann_ode_and_acceleration_constructive`, proving:
1. `0 < H₀`, `q₀ ∈ (-1, 0)`, and `q₀ = -mannheimOmegaLambdaBar S₀ lam k t`;
2. `d_L(0) = 0`, `0 < conformalRadicand q₀ z` and `0 < d_L(z)` for all `z > 0`;
3. `d_L'(0) = c / H₀` and `d_L''(0) = (c / H₀) * (1 - q₀) > c / H₀`;
4. Closed-form conformal horizon `conformalHorizon c S₀ lam k t_i t` and divergence to `+∞`
   as `t_i → 0⁺`. -/
theorem mannheim_friedmann_luminosity_horizon_instantiation
    {c S₀ lam k t : ℝ} (hc : 0 < c) (hS : S₀ ≠ 0) (hlam : 0 < lam)
    (hk : k < 0) (ht : 0 < t) :
    let H₀ := mannheimHubble S₀ lam k t
    let q₀ := mannheimDeceleration S₀ lam k t
    0 < H₀ ∧
    q₀ ∈ Set.Ioo (-1 : ℝ) 0 ∧
    q₀ = -mannheimOmegaLambdaBar S₀ lam k t ∧
    conformalLuminosityDist c H₀ q₀ 0 = 0 ∧
    (∀ z : ℝ, 0 < z → 0 < conformalRadicand q₀ z ∧ 0 < conformalLuminosityDist c H₀ q₀ z) ∧
    deriv (conformalLuminosityDist c H₀ q₀) 0 = c / H₀ ∧
    iteratedDeriv 1 (conformalLuminosityDist c H₀ q₀) 0 = c / H₀ ∧
    deriv (deriv (conformalLuminosityDist c H₀ q₀)) 0 = (c / H₀) * (1 - q₀) ∧
    iteratedDeriv 2 (conformalLuminosityDist c H₀ q₀) 0 = (c / H₀) * (1 - q₀) ∧
    c / H₀ < (c / H₀) * (1 - q₀) ∧
    (∀ t_i : ℝ, 0 < t_i →
      conformalHorizon c S₀ lam k t_i t =
        (c / Real.sqrt (-k)) *
          (Real.log (Real.tanh (mannheimCosmoRate S₀ lam * t / 2)) -
           Real.log (Real.tanh (mannheimCosmoRate S₀ lam * t_i / 2)))) ∧
    Tendsto (fun t_i => conformalHorizon c S₀ lam k t_i t) (𝓝[>] 0) Filter.atTop := by
  intro H₀ q₀
  obtain ⟨_, _, _, _, _, hH_pos, _, _, _, _, _, hq_eq, hq_gt, hq_lt⟩ :=
    mannheim_conformal_friedmann_ode_and_acceleration_constructive S₀ lam k t hS hlam hk ht
  have hq_mem : q₀ ∈ Set.Ioo (-1 : ℝ) 0 := ⟨hq_gt, hq_lt⟩
  have hd1 := conformalLuminosityDist_deriv1_zero (c := c) hH_pos.ne' hq_mem
  have hd2 := conformalLuminosityDist_deriv2_zero hc hH_pos hq_mem
  have hhor := conformalHorizon_eq_and_tendsto_atTop hc hS hlam hk ht
  refine ⟨hH_pos, hq_mem, hq_eq, conformalLuminosityDist_zero c H₀ q₀, ?_,
    hd1.1, hd1.2, hd2.1, hd2.2.1, hd2.2.2, hhor.1, hhor.2⟩
  intro z hz
  exact ⟨conformalRadicand_pos hq_mem (by linarith),
    conformalLuminosityDist_pos hc hH_pos hq_mem hz⟩

end InfoGeometry.Conformal.MannheimConformalLuminosityHorizon
