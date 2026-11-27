/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.NumberTheory.SumPrimeReciprocals
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Order.Hom.Set

/-!
# Weierstrass–Mandelbrot, Wu–Sprung & Riemann–Liouville Fractional Operators (Castro 2006 §2)

Formalizes the analytic building blocks of Castro (2006) §2, Eqs. (2)–(15):
1. `CastroFractalParams` and constructive default witness `castroDefaultParams` (`D = 3/2`,
   `γ = 2`, `V₀ = 3.10073 * π`, `β = D / 2 = 3/4`).
2. Weierstrass–Mandelbrot series `W(x, γ, D, α)` and sine series: geometric M-test uniform
   convergence and continuity on `ℝ` for `1 < D < 2`, `1 < γ`.
3. Prime-weighted Weierstrass series: uniform convergence on `Set.Ici x₀` (`2 < x₀`) and compact
   subsets of `Set.Ioi 2`, continuity on `Set.Ioi 2`, and exact divergence boundary `x ≤ 2`.
   For Eq. (8)'s symmetrization `W(x) + W(-x)`, simultaneous absolute convergence of the prime
   weights requires `2 < |x|`.
4. Wu–Sprung coordinate map `x(V)`: positivity of `dx/dV` for `V₀ < V` (`2 * π < V₀`),
   `StrictMonoOn` on `Set.Ici V₀`, divergence to `+∞`, `OrderIso`, and inverse potential `wuSprungV`.
5. Riemann–Liouville fractional integrals `I_L^α`, `I_R^α` and derivatives `D_L^β`, `D_R^β` on
   finite endpoints: integrability, linearity, power-function formulas, semigroup law, left–right
   adjointness, and explicit non-Hermiticity and `[D_L^β, X] ≠ 0` witnesses.
-/

noncomputable section

namespace InfoGeometry.Analysis.WeierstrassFractalAndFractionalDeriv

open Real Filter MeasureTheory Set
open scoped BigOperators Topology Interval

/-! ## Section 1: Fractal SUSY-QM Parameters and Constructive Witness -/

/-- Parameter record for Castro (2006) §2 fractal SUSY-QM constructions: fractal dimension
`1 < D < 2`, Weierstrass scaling `1 < γ`, and Wu–Sprung threshold `2 * π < V₀`. -/
structure CastroFractalParams where
  D : ℝ
  γ : ℝ
  V₀ : ℝ
  hD_gt : 1 < D
  hD_lt : D < 2
  hγ : 1 < γ
  hV₀ : 2 * Real.pi < V₀

/-- Fractional derivative order `β = D / 2` (Castro 2006 §2, Eq. 7). -/
def CastroFractalParams.β (p : CastroFractalParams) : ℝ :=
  p.D / 2

theorem CastroFractalParams.β_pos (p : CastroFractalParams) : 0 < p.β := by
  unfold CastroFractalParams.β
  linarith [p.hD_gt]

theorem CastroFractalParams.β_lt_one (p : CastroFractalParams) : p.β < 1 := by
  unfold CastroFractalParams.β
  linarith [p.hD_lt]

/-- Constructive default parameter witness (`D = 3/2`, `γ = 2`, `V₀ = 3.10073 * π`). -/
def castroDefaultParams : CastroFractalParams where
  D := 3 / 2
  γ := 2
  V₀ := 3.10073 * Real.pi
  hD_gt := by norm_num
  hD_lt := by norm_num
  hγ := by norm_num
  hV₀ := by linarith [Real.pi_pos]

theorem castroDefaultParams_β : castroDefaultParams.β = 3 / 4 := by
  simp [CastroFractalParams.β, castroDefaultParams]
  norm_num

/-! ## Section 2: Weierstrass–Mandelbrot Fractal Series (Castro Eqs. 2 & 10) -/

/-- Summand of the complex Weierstrass–Mandelbrot fractal function (Castro Eq. 2). -/
def weierstrassMandelbrotTerm (γ D : ℝ) (α : ℕ → ℝ) (n : ℕ) (x : ℝ) : ℂ :=
  ((1 - Complex.exp (Complex.I * (x : ℂ) * ((γ : ℂ) ^ n))) /
      ((γ ^ ((n : ℝ) * (2 - D)) : ℝ) : ℂ)) *
    Complex.exp (Complex.I * (α n : ℂ))

/-- Complex Weierstrass–Mandelbrot fractal function `W(x, γ, D, α)` (Castro Eq. 2). -/
def weierstrassMandelbrot (x γ D : ℝ) (α : ℕ → ℝ) : ℂ :=
  ∑' n : ℕ, weierstrassMandelbrotTerm γ D α n x

/-- Summand of the real sine Weierstrass series (Castro Eq. 10). -/
def weierstrassSinTerm (γ D : ℝ) (α : ℕ → ℝ) (m : ℕ) (x : ℝ) : ℝ :=
  Real.sin (γ ^ m * x + α m) / γ ^ ((m : ℝ) * (2 - D))

/-- Real sine Weierstrass fractal function (Castro Eq. 10). -/
def weierstrassSin (x γ D : ℝ) (α : ℕ → ℝ) : ℝ :=
  ∑' m : ℕ, weierstrassSinTerm γ D α m x

private theorem rpow_neg_mul_nat_eq_geom {γ D : ℝ} (hγ : 1 < γ) (n : ℕ) :
    (γ ^ ((n : ℝ) * (2 - D)))⁻¹ = (γ ^ (-(2 - D))) ^ n := by
  have hγ0 : 0 ≤ γ := by linarith [hγ]
  rw [← Real.rpow_neg hγ0, ← Real.rpow_natCast (γ ^ (-(2 - D))) n, ← Real.rpow_mul hγ0]
  congr 1
  ring

private theorem summable_weierstrass_geom {γ D : ℝ} (hD_lt : D < 2) (hγ : 1 < γ) :
    Summable (fun n : ℕ => (γ ^ (-(2 - D))) ^ n) := by
  have hγ0 : 0 ≤ γ := by linarith [hγ]
  have hr_nonneg : 0 ≤ γ ^ (-(2 - D)) := Real.rpow_nonneg hγ0 _
  have hr_lt_one : γ ^ (-(2 - D)) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg hγ (by linarith [hD_lt])
  exact summable_geometric_of_lt_one hr_nonneg hr_lt_one

private theorem norm_exp_I_real (θ : ℝ) : ‖Complex.exp (Complex.I * (θ : ℂ))‖ = 1 := by
  rw [mul_comm]
  exact Complex.norm_exp_ofReal_mul_I θ

theorem weierstrassMandelbrotTerm_norm_le {γ D : ℝ} (hγ : 1 < γ) (α : ℕ → ℝ) (n : ℕ) (x : ℝ) :
    ‖weierstrassMandelbrotTerm γ D α n x‖ ≤ 2 * (γ ^ (-(2 - D))) ^ n := by
  have hγ0 : 0 < γ := by linarith
  have hpow_pos : 0 < γ ^ ((n : ℝ) * (2 - D)) := Real.rpow_pos_of_pos hγ0 _
  have harg : Complex.I * (x : ℂ) * ((γ : ℂ) ^ n) = Complex.I * ((x * γ ^ n : ℝ) : ℂ) := by
    push_cast
    ring
  have hexp1 : ‖Complex.exp (Complex.I * (x : ℂ) * ((γ : ℂ) ^ n))‖ = 1 := by
    rw [harg]
    exact norm_exp_I_real (x * γ ^ n)
  have hnum : ‖1 - Complex.exp (Complex.I * (x : ℂ) * ((γ : ℂ) ^ n))‖ ≤ 2 := by
    calc
      ‖1 - Complex.exp (Complex.I * (x : ℂ) * ((γ : ℂ) ^ n))‖
          ≤ ‖(1 : ℂ)‖ + ‖Complex.exp (Complex.I * (x : ℂ) * ((γ : ℂ) ^ n))‖ :=
        norm_sub_le _ _
      _ = 2 := by rw [norm_one, hexp1]; norm_num
  have hexp2 : ‖Complex.exp (Complex.I * (α n : ℂ))‖ = 1 := norm_exp_I_real (α n)
  unfold weierstrassMandelbrotTerm
  rw [norm_mul, norm_div, hexp2, mul_one, Complex.norm_real,
    Real.norm_of_nonneg hpow_pos.le, div_eq_mul_inv, rpow_neg_mul_nat_eq_geom hγ n]
  exact mul_le_mul_of_nonneg_right hnum (pow_nonneg (Real.rpow_nonneg hγ0.le _) n)

theorem weierstrassMandelbrot_tendstoUniformly {γ D : ℝ} (hD_lt : D < 2) (hγ : 1 < γ)
    (α : ℕ → ℝ) :
    TendstoUniformly
      (fun t : Finset ℕ => fun x : ℝ => ∑ n ∈ t, weierstrassMandelbrotTerm γ D α n x)
      (fun x : ℝ => weierstrassMandelbrot x γ D α) atTop :=
  tendstoUniformly_tsum ((summable_weierstrass_geom hD_lt hγ).mul_left 2)
    (fun n x => weierstrassMandelbrotTerm_norm_le hγ α n x)

theorem weierstrassMandelbrot_continuous {γ D : ℝ} (hD_lt : D < 2) (hγ : 1 < γ) (α : ℕ → ℝ) :
    Continuous (fun x : ℝ => weierstrassMandelbrot x γ D α) := by
  refine continuous_tsum ?_ ((summable_weierstrass_geom hD_lt hγ).mul_left 2)
    (fun n x => weierstrassMandelbrotTerm_norm_le hγ α n x)
  intro n
  unfold weierstrassMandelbrotTerm
  fun_prop

theorem weierstrassSinTerm_norm_le {γ D : ℝ} (hγ : 1 < γ) (α : ℕ → ℝ) (m : ℕ) (x : ℝ) :
    ‖weierstrassSinTerm γ D α m x‖ ≤ (γ ^ (-(2 - D))) ^ m := by
  have hγ0 : 0 < γ := by linarith
  have hpow_pos : 0 < γ ^ ((m : ℝ) * (2 - D)) := Real.rpow_pos_of_pos hγ0 _
  unfold weierstrassSinTerm
  rw [Real.norm_eq_abs, abs_div, abs_of_pos hpow_pos, div_eq_mul_inv,
    rpow_neg_mul_nat_eq_geom hγ m]
  calc
    |Real.sin (γ ^ m * x + α m)| * (γ ^ (-(2 - D))) ^ m
        ≤ 1 * (γ ^ (-(2 - D))) ^ m :=
      mul_le_mul_of_nonneg_right (Real.abs_sin_le_one _)
        (pow_nonneg (Real.rpow_nonneg hγ0.le _) m)
    _ = (γ ^ (-(2 - D))) ^ m := one_mul _

theorem weierstrassSin_tendstoUniformly {γ D : ℝ} (hD_lt : D < 2) (hγ : 1 < γ) (α : ℕ → ℝ) :
    TendstoUniformly
      (fun t : Finset ℕ => fun x : ℝ => ∑ m ∈ t, weierstrassSinTerm γ D α m x)
      (fun x : ℝ => weierstrassSin x γ D α) atTop :=
  tendstoUniformly_tsum (summable_weierstrass_geom hD_lt hγ)
    (fun m x => weierstrassSinTerm_norm_le hγ α m x)

theorem weierstrassSin_continuous {γ D : ℝ} (hD_lt : D < 2) (hγ : 1 < γ) (α : ℕ → ℝ) :
    Continuous (fun x : ℝ => weierstrassSin x γ D α) := by
  refine continuous_tsum ?_ (summable_weierstrass_geom hD_lt hγ)
    (fun m x => weierstrassSinTerm_norm_le hγ α m x)
  intro m
  unfold weierstrassSinTerm
  fun_prop

/-! ## Section 3: Prime-Weighted Weierstrass Series & `x ≤ 2` Divergence Boundary (Castro Eqs. 3, 8, 9) -/

/-- Inner prime-frequency Weierstrass sum for prime `p` (Castro Eqs. 3 & 9). -/
def primeWeierstrassInner (D : ℝ) (α : ℕ → ℝ) (p : Nat.Primes) (x : ℝ) : ℝ :=
  ∑' m : ℕ, Real.sin ((p : ℝ) ^ m * x + α m) / (p : ℝ) ^ ((m : ℝ) * (2 - D))

/-- Outer prime-weighted summand `p^{-x/2} * W_p(x)` (Castro Eqs. 3 & 9). -/
def primeWeierstrassTerm (D : ℝ) (α : ℕ → ℝ) (p : Nat.Primes) (x : ℝ) : ℝ :=
  (p : ℝ) ^ (-x / 2) * primeWeierstrassInner D α p x

/-- Prime-weighted Weierstrass fluctuating potential `W(x)` (Castro Eqs. 3 & 9).
Absolute convergence of the prime weights `p^{-x/2}` holds iff `2 < x`. Consequently, for
Castro Eq. (8)'s symmetrization `W(x) + W(-x)`, simultaneous absolute convergence of the prime
sum holds for `2 < |x|` and fails on `[-2, 2]`. -/
def primeWeierstrass (W₀ D : ℝ) (α : ℕ → ℝ) (x : ℝ) : ℝ :=
  W₀ * ∑' p : Nat.Primes, primeWeierstrassTerm D α p x

private theorem prime_two_le (p : Nat.Primes) : (2 : ℝ) ≤ (p : ℝ) := by
  exact_mod_cast p.prop.two_le

private theorem primeWeierstrassInner_term_norm_le {D : ℝ} (hD_lt : D < 2) (α : ℕ → ℝ)
    (p : Nat.Primes) (m : ℕ) (x : ℝ) :
    ‖Real.sin ((p : ℝ) ^ m * x + α m) / (p : ℝ) ^ ((m : ℝ) * (2 - D))‖ ≤
      ((2 : ℝ) ^ (-(2 - D))) ^ m := by
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := prime_two_le p
  have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
  have hexp_nonneg : 0 ≤ (m : ℝ) * (2 - D) :=
    mul_nonneg (Nat.cast_nonneg m) (by linarith [hD_lt])
  have hpow_le : (2 : ℝ) ^ ((m : ℝ) * (2 - D)) ≤ (p : ℝ) ^ ((m : ℝ) * (2 - D)) :=
    Real.rpow_le_rpow (by norm_num) hp2 hexp_nonneg
  have h2pow_pos : (0 : ℝ) < (2 : ℝ) ^ ((m : ℝ) * (2 - D)) := Real.rpow_pos_of_pos (by norm_num) _
  have hppow_pos : (0 : ℝ) < (p : ℝ) ^ ((m : ℝ) * (2 - D)) := Real.rpow_pos_of_pos hp0 _
  rw [Real.norm_eq_abs, abs_div, abs_of_pos hppow_pos]
  calc
    |Real.sin ((p : ℝ) ^ m * x + α m)| / (p : ℝ) ^ ((m : ℝ) * (2 - D))
        ≤ 1 / (p : ℝ) ^ ((m : ℝ) * (2 - D)) :=
      div_le_div_of_nonneg_right (Real.abs_sin_le_one _) hppow_pos.le
    _ ≤ 1 / (2 : ℝ) ^ ((m : ℝ) * (2 - D)) :=
      one_div_le_one_div_of_le h2pow_pos hpow_le
    _ = ((2 : ℝ) ^ (-(2 - D))) ^ m := by
      rw [one_div, rpow_neg_mul_nat_eq_geom (γ := 2) (by norm_num) m]

private theorem summable_two_rpow_neg {D : ℝ} (hD_lt : D < 2) :
    Summable (fun m : ℕ => ((2 : ℝ) ^ (-(2 - D))) ^ m) :=
  summable_weierstrass_geom hD_lt (γ := 2) (by norm_num)

theorem primeWeierstrassInner_continuous {D : ℝ} (hD_lt : D < 2) (α : ℕ → ℝ)
    (p : Nat.Primes) : Continuous (primeWeierstrassInner D α p) := by
  refine continuous_tsum ?_ (summable_two_rpow_neg hD_lt)
    (fun m x => primeWeierstrassInner_term_norm_le hD_lt α p m x)
  intro m
  fun_prop

theorem primeWeierstrassInner_norm_le {D : ℝ} (hD_lt : D < 2) (α : ℕ → ℝ) (p : Nat.Primes)
    (x : ℝ) :
    ‖primeWeierstrassInner D α p x‖ ≤ ∑' m : ℕ, ((2 : ℝ) ^ (-(2 - D))) ^ m := by
  have hsum :
      Summable (fun m : ℕ => ‖Real.sin ((p : ℝ) ^ m * x + α m) / (p : ℝ) ^ ((m : ℝ) * (2 - D))‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
      (fun m => primeWeierstrassInner_term_norm_le hD_lt α p m x) (summable_two_rpow_neg hD_lt)
  calc
    ‖primeWeierstrassInner D α p x‖
        ≤ ∑' m : ℕ, ‖Real.sin ((p : ℝ) ^ m * x + α m) / (p : ℝ) ^ ((m : ℝ) * (2 - D))‖ :=
      norm_tsum_le_tsum_norm hsum
    _ ≤ ∑' m : ℕ, ((2 : ℝ) ^ (-(2 - D))) ^ m :=
      hsum.tsum_le_tsum (fun m => primeWeierstrassInner_term_norm_le hD_lt α p m x)
        (summable_two_rpow_neg hD_lt)

/-- Exact convergence/divergence boundary for the prime weights `p^{-x/2}`: summable iff `2 < x`. -/
theorem primeAmplitude_summable_iff (x : ℝ) :
    Summable (fun p : Nat.Primes => (p : ℝ) ^ (-x / 2)) ↔ 2 < x := by
  rw [Nat.Primes.summable_rpow]
  constructor <;> intro h <;> linarith

theorem primeAmplitude_not_summable_of_le_two {x : ℝ} (hx : x ≤ 2) :
    ¬ Summable (fun p : Nat.Primes => (p : ℝ) ^ (-x / 2)) := by
  rw [primeAmplitude_summable_iff]
  linarith [hx]

theorem primeAmplitude_at_two_eq_one_div (p : Nat.Primes) :
    (p : ℝ) ^ (-(2 : ℝ) / 2) = 1 / (p : ℝ) := by
  rw [show -(2 : ℝ) / 2 = -1 by norm_num, Real.rpow_neg_one, one_div]

theorem primeAmplitude_not_summable_at_two :
    ¬ Summable (fun p : Nat.Primes => (p : ℝ) ^ (-(2 : ℝ) / 2)) := by
  simpa only [primeAmplitude_at_two_eq_one_div] using Nat.Primes.not_summable_one_div

/-- Explicit divergence witness at `x = 0` with `α = fun _ => π / 2`: each prime summand
is at least `1`, so the outer prime series cannot be summable. -/
theorem primeWeierstrass_not_summable_at_zero {D : ℝ} (hD_lt : D < 2) :
    ¬ Summable (fun p : Nat.Primes => primeWeierstrassTerm D (fun _ => Real.pi / 2) p 0) := by
  intro hsum
  have hlim :
      Filter.Tendsto (fun p : Nat.Primes => primeWeierstrassTerm D (fun _ => Real.pi / 2) p 0)
        Filter.cofinite (𝓝 0) :=
    hsum.tendsto_cofinite_zero
  have hge :
      ∀ p : Nat.Primes, 1 ≤ primeWeierstrassTerm D (fun _ => Real.pi / 2) p 0 := by
    intro p
    have hp0 : (0 : ℝ) < (p : ℝ) := by linarith [prime_two_le p]
    have hinner_sum :
        Summable (fun m : ℕ =>
          Real.sin ((p : ℝ) ^ m * 0 + Real.pi / 2) / (p : ℝ) ^ ((m : ℝ) * (2 - D))) := by
      refine Summable.of_norm_bounded (summable_two_rpow_neg hD_lt) ?_
      intro m
      exact primeWeierstrassInner_term_norm_le hD_lt (fun _ => Real.pi / 2) p m 0
    have hterm_nonneg :
        ∀ m : ℕ,
          0 ≤ Real.sin ((p : ℝ) ^ m * 0 + Real.pi / 2) / (p : ℝ) ^ ((m : ℝ) * (2 - D)) := by
      intro m
      rw [mul_zero, zero_add, Real.sin_pi_div_two]
      exact div_nonneg zero_le_one (Real.rpow_nonneg hp0.le _)
    have h0_le :
        Real.sin ((p : ℝ) ^ 0 * 0 + Real.pi / 2) / (p : ℝ) ^ ((0 : ℕ) * (2 - D)) ≤
          primeWeierstrassInner D (fun _ => Real.pi / 2) p 0 :=
      hinner_sum.le_tsum 0 (fun m _ => hterm_nonneg m)
    have h0_eq :
        Real.sin ((p : ℝ) ^ 0 * 0 + Real.pi / 2) / (p : ℝ) ^ (((0 : ℕ) : ℝ) * (2 - D)) = 1 := by
      simp
    unfold primeWeierstrassTerm
    rw [show -(0 : ℝ) / 2 = 0 by norm_num, Real.rpow_zero, one_mul]
    linarith [h0_le, h0_eq]
  have hev : ∀ᶠ p : Nat.Primes in Filter.cofinite,
      primeWeierstrassTerm D (fun _ => Real.pi / 2) p 0 < 1 :=
    hlim (Iio_mem_nhds one_pos)
  obtain ⟨p, hp⟩ := hev.exists
  linarith [hge p]

private theorem primeWeierstrassTerm_norm_le_of_Ici {D x₀ : ℝ} (hD_lt : D < 2) (α : ℕ → ℝ)
    (p : Nat.Primes) {x : ℝ} (hx : x₀ ≤ x) :
    ‖primeWeierstrassTerm D α p x‖ ≤
      (∑' m : ℕ, ((2 : ℝ) ^ (-(2 - D))) ^ m) * (p : ℝ) ^ (-x₀ / 2) := by
  have hp1 : (1 : ℝ) ≤ (p : ℝ) := by linarith [prime_two_le p]
  have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
  have hpow_le : (p : ℝ) ^ (-x / 2) ≤ (p : ℝ) ^ (-x₀ / 2) :=
    Real.rpow_le_rpow_of_exponent_le hp1 (by linarith [hx])
  have hpow_pos : 0 < (p : ℝ) ^ (-x / 2) := Real.rpow_pos_of_pos hp0 _
  unfold primeWeierstrassTerm
  rw [norm_mul, Real.norm_eq_abs, abs_of_pos hpow_pos, mul_comm]
  exact mul_le_mul (primeWeierstrassInner_norm_le hD_lt α p x) hpow_le hpow_pos.le
    (tsum_nonneg fun m => pow_nonneg (Real.rpow_nonneg (by norm_num) _) m)

private theorem summable_prime_majorant {D x₀ : ℝ} (hx₀ : 2 < x₀) :
    Summable (fun p : Nat.Primes =>
      (∑' m : ℕ, ((2 : ℝ) ^ (-(2 - D))) ^ m) * (p : ℝ) ^ (-x₀ / 2)) :=
  ((primeAmplitude_summable_iff x₀).mpr hx₀).mul_left _

theorem primeWeierstrass_tendstoUniformlyOn_Ici {D x₀ : ℝ} (hD_lt : D < 2) (hx₀ : 2 < x₀)
    (α : ℕ → ℝ) :
    TendstoUniformlyOn
      (fun t : Finset Nat.Primes => fun x : ℝ => ∑ p ∈ t, primeWeierstrassTerm D α p x)
      (fun x : ℝ => ∑' p : Nat.Primes, primeWeierstrassTerm D α p x) atTop (Set.Ici x₀) :=
  tendstoUniformlyOn_tsum (summable_prime_majorant hx₀)
    (fun p _ hx => primeWeierstrassTerm_norm_le_of_Ici hD_lt α p hx)

theorem primeWeierstrass_tendstoUniformlyOn_compact {D : ℝ} (hD_lt : D < 2) (α : ℕ → ℝ)
    {K : Set ℝ} (hK : IsCompact K) (hK_sub : K ⊆ Set.Ioi 2) :
    TendstoUniformlyOn
      (fun t : Finset Nat.Primes => fun x : ℝ => ∑ p ∈ t, primeWeierstrassTerm D α p x)
      (fun x : ℝ => ∑' p : Nat.Primes, primeWeierstrassTerm D α p x) atTop K := by
  rcases K.eq_empty_or_nonempty with rfl | hne
  · simp [TendstoUniformlyOn]
  · obtain ⟨x₀, hx₀K, hx₀min⟩ := hK.exists_isMinOn hne continuousOn_id
    have hx₀ : 2 < x₀ := hK_sub hx₀K
    exact (primeWeierstrass_tendstoUniformlyOn_Ici hD_lt hx₀ α).mono
      (fun x hx => hx₀min hx)

theorem primeWeierstrass_continuousOn_Ici {W₀ D x₀ : ℝ} (hD_lt : D < 2) (hx₀ : 2 < x₀)
    (α : ℕ → ℝ) :
    ContinuousOn (primeWeierstrass W₀ D α) (Set.Ici x₀) := by
  refine continuousOn_const.mul ?_
  refine continuousOn_tsum ?_ (summable_prime_majorant hx₀)
    (fun p _ hx => primeWeierstrassTerm_norm_le_of_Ici hD_lt α p hx)
  intro p
  refine Continuous.continuousOn ?_
  unfold primeWeierstrassTerm
  have hp0 : (p : ℝ) ≠ 0 := by linarith [prime_two_le p]
  refine Continuous.mul ?_ (primeWeierstrassInner_continuous hD_lt α p)
  exact Continuous.rpow continuous_const (continuous_neg.div_const 2) (fun _ => Or.inl hp0)

theorem primeWeierstrass_continuousOn_Ioi_two {W₀ D : ℝ} (hD_lt : D < 2) (α : ℕ → ℝ) :
    ContinuousOn (primeWeierstrass W₀ D α) (Set.Ioi 2) := by
  intro x hx
  have hx' : 2 < x := hx
  let x₀ : ℝ := (2 + x) / 2
  have hx₀ : 2 < x₀ := by simp only [x₀]; linarith
  have hx_gt : x₀ < x := by simp only [x₀]; linarith
  have hcont := (primeWeierstrass_continuousOn_Ici (W₀ := W₀) hD_lt hx₀ α) x hx_gt.le
  exact ContinuousWithinAt.mono_of_mem_nhdsWithin hcont
    (mem_nhdsWithin_of_mem_nhds (Ici_mem_nhds hx_gt))

/-! ## Section 4: Wu–Sprung Coordinate Map `x(V)` & Inverse Potential `V_WS` (Castro Eq. 4) -/

/-- Wu–Sprung threshold parameter `V₀ = 3.10073 * π` (Castro 2006 §2, Eq. 4). -/
def wuSprungV₀ : ℝ :=
  3.10073 * Real.pi

theorem wuSprungV₀_gt_two_pi : 2 * Real.pi < wuSprungV₀ := by
  unfold wuSprungV₀
  linarith [Real.pi_pos]

/-- Constant `ln(V₀ / (2πe²))` in the Wu–Sprung coordinate expression (Castro Eq. 4). -/
def wuSprungConst (V₀ : ℝ) : ℝ :=
  Real.log (V₀ / (2 * Real.pi * Real.exp 2))

/-- Normalized Wu–Sprung coordinate expression in `y = V / V₀` (Castro Eq. 4). -/
def wuSprungNormalized (V₀ y : ℝ) : ℝ :=
  Real.sqrt (y - 1) * wuSprungConst V₀ +
    Real.sqrt y * Real.log ((Real.sqrt y + Real.sqrt (y - 1)) / (Real.sqrt y - Real.sqrt (y - 1)))

/-- Wu–Sprung coordinate `x(V)` (Castro Eq. 4). -/
def wuSprungX (V₀ V : ℝ) : ℝ :=
  (Real.sqrt V₀ / Real.pi) * wuSprungNormalized V₀ (V / V₀)

private theorem wuSprungConst_add_two {V₀ : ℝ} (hV₀ : 0 < V₀) :
    wuSprungConst V₀ + 2 = Real.log (V₀ / (2 * Real.pi)) := by
  have hpi : 0 < 2 * Real.pi := by positivity
  have hexp : 0 < Real.exp 2 := Real.exp_pos 2
  have hden : 2 * Real.pi * Real.exp 2 ≠ 0 := by positivity
  unfold wuSprungConst
  rw [Real.log_div hV₀.ne' hden, Real.log_mul hpi.ne' hexp.ne', Real.log_exp,
    Real.log_div hV₀.ne' hpi.ne']
  ring

private theorem sqrt_sub_sqrt_pos {y : ℝ} (hy : 1 ≤ y) :
    0 < Real.sqrt y - Real.sqrt (y - 1) := by
  have hlt : y - 1 < y := by linarith
  have hsqrt : Real.sqrt (y - 1) < Real.sqrt y := Real.sqrt_lt_sqrt (by linarith [hy]) hlt
  linarith

private theorem sqrt_add_div_sqrt_sub_eq {y : ℝ} (hy : 1 ≤ y) :
    (Real.sqrt y + Real.sqrt (y - 1)) / (Real.sqrt y - Real.sqrt (y - 1)) =
      (Real.sqrt y + Real.sqrt (y - 1)) ^ 2 := by
  have hsub_pos : 0 < Real.sqrt y - Real.sqrt (y - 1) := sqrt_sub_sqrt_pos hy
  have hmul :
      (Real.sqrt y + Real.sqrt (y - 1)) * (Real.sqrt y - Real.sqrt (y - 1)) = 1 := by
    have h1 : Real.sqrt y * Real.sqrt y = y := Real.mul_self_sqrt (by linarith)
    have h2 : Real.sqrt (y - 1) * Real.sqrt (y - 1) = y - 1 := Real.mul_self_sqrt (by linarith)
    linarith [show (Real.sqrt y + Real.sqrt (y - 1)) * (Real.sqrt y - Real.sqrt (y - 1)) =
      Real.sqrt y * Real.sqrt y - Real.sqrt (y - 1) * Real.sqrt (y - 1) by ring]
  rw [div_eq_iff hsub_pos.ne']
  calc
    Real.sqrt y + Real.sqrt (y - 1)
        = (Real.sqrt y + Real.sqrt (y - 1)) *
            ((Real.sqrt y + Real.sqrt (y - 1)) * (Real.sqrt y - Real.sqrt (y - 1))) := by
          rw [hmul, mul_one]
    _ = (Real.sqrt y + Real.sqrt (y - 1)) ^ 2 * (Real.sqrt y - Real.sqrt (y - 1)) := by ring

private theorem wuSprungNormalized_eq_simplified {V₀ y : ℝ} (hy : 1 ≤ y) :
    wuSprungNormalized V₀ y =
      Real.sqrt (y - 1) * wuSprungConst V₀ +
        Real.sqrt y * (2 * Real.log (Real.sqrt y + Real.sqrt (y - 1))) := by
  unfold wuSprungNormalized
  rw [sqrt_add_div_sqrt_sub_eq hy]
  have hpos : 0 < Real.sqrt y + Real.sqrt (y - 1) := by
    have : 0 < Real.sqrt y := Real.sqrt_pos.mpr (by linarith)
    linarith [Real.sqrt_nonneg (y - 1)]
  rw [Real.log_pow, Nat.cast_ofNat]

private theorem hasDerivAt_wuSprungNormalized {V₀ y : ℝ} (hV₀ : 0 < V₀) (hy : 1 < y) :
    HasDerivAt (wuSprungNormalized V₀)
      (Real.log (V₀ / (2 * Real.pi)) / (2 * Real.sqrt (y - 1)) +
        Real.log (Real.sqrt y + Real.sqrt (y - 1)) / Real.sqrt y) y := by
  have hy0 : y ≠ 0 := by linarith
  have hy1 : y - 1 ≠ 0 := by linarith
  have hsy : 0 < Real.sqrt y := Real.sqrt_pos.mpr (by linarith)
  have hsy1 : 0 < Real.sqrt (y - 1) := Real.sqrt_pos.mpr (by linarith)
  have hsum_pos : 0 < Real.sqrt y + Real.sqrt (y - 1) := by linarith
  have hd_sy : HasDerivAt Real.sqrt (1 / (2 * Real.sqrt y)) y :=
    (hasDerivAt_id y).sqrt hy0
  have hd_sy1 : HasDerivAt (fun t : ℝ => Real.sqrt (t - 1)) (1 / (2 * Real.sqrt (y - 1))) y := by
    simpa using ((hasDerivAt_id y).sub_const 1).sqrt hy1
  have hd_sum :
      HasDerivAt (fun t : ℝ => Real.sqrt t + Real.sqrt (t - 1))
        (1 / (2 * Real.sqrt y) + 1 / (2 * Real.sqrt (y - 1))) y :=
    hd_sy.add hd_sy1
  have hd_log :
      HasDerivAt (fun t : ℝ => Real.log (Real.sqrt t + Real.sqrt (t - 1)))
        ((1 / (2 * Real.sqrt y) + 1 / (2 * Real.sqrt (y - 1))) /
          (Real.sqrt y + Real.sqrt (y - 1))) y :=
    hd_sum.log hsum_pos.ne'
  have hd_term1 :
      HasDerivAt (fun t : ℝ => Real.sqrt (t - 1) * wuSprungConst V₀)
        ((1 / (2 * Real.sqrt (y - 1))) * wuSprungConst V₀) y :=
    hd_sy1.mul_const (wuSprungConst V₀)
  have hd_term2 :
      HasDerivAt (fun t : ℝ => Real.sqrt t * (2 * Real.log (Real.sqrt t + Real.sqrt (t - 1))))
        ((1 / (2 * Real.sqrt y)) * (2 * Real.log (Real.sqrt y + Real.sqrt (y - 1))) +
          Real.sqrt y * (2 * ((1 / (2 * Real.sqrt y) + 1 / (2 * Real.sqrt (y - 1))) /
            (Real.sqrt y + Real.sqrt (y - 1))))) y :=
    hd_sy.mul (hd_log.const_mul 2)
  have hd_simp := hd_term1.add hd_term2
  have hev :
      (fun t : ℝ => Real.sqrt (t - 1) * wuSprungConst V₀ +
        Real.sqrt t * (2 * Real.log (Real.sqrt t + Real.sqrt (t - 1)))) =ᶠ[𝓝 y]
        wuSprungNormalized V₀ := by
    filter_upwards [Ioi_mem_nhds hy] with t ht
    exact (wuSprungNormalized_eq_simplified (le_of_lt ht)).symm
  have hd := hd_simp.congr_of_eventuallyEq hev.symm
  convert hd using 1
  have hC : wuSprungConst V₀ = Real.log (V₀ / (2 * Real.pi)) - 2 := by
    linarith [wuSprungConst_add_two hV₀]
  rw [hC]
  field_simp [hsy.ne', hsy1.ne', hsum_pos.ne']
  ring

theorem wuSprungX_hasDerivAt {V₀ V : ℝ} (hV₀ : 2 * Real.pi < V₀) (hV : V₀ < V) :
    HasDerivAt (wuSprungX V₀)
      ((Real.sqrt V₀ / Real.pi) *
        (Real.log (V₀ / (2 * Real.pi)) / (2 * Real.sqrt (V / V₀ - 1)) +
          Real.log (Real.sqrt (V / V₀) + Real.sqrt (V / V₀ - 1)) / Real.sqrt (V / V₀)) *
        V₀⁻¹) V := by
  have hV₀_pos : 0 < V₀ := by linarith [hV₀, Real.pi_pos]
  have hy_gt : 1 < V / V₀ := (one_lt_div hV₀_pos).mpr hV
  have hd_div : HasDerivAt (fun t : ℝ => t / V₀) V₀⁻¹ V := by
    have hd0 := (hasDerivAt_id V).mul_const V₀⁻¹
    simpa only [div_eq_mul_inv, id_eq, one_mul] using hd0
  have hd_norm := (hasDerivAt_wuSprungNormalized hV₀_pos hy_gt).comp V hd_div
  have hd_mul := hd_norm.const_mul (Real.sqrt V₀ / Real.pi)
  change HasDerivAt (fun t : ℝ => (Real.sqrt V₀ / Real.pi) * wuSprungNormalized V₀ (t / V₀)) _ V
  convert hd_mul using 1
  · ext t; simp
  · ring

theorem wuSprungX_deriv_pos {V₀ V : ℝ} (hV₀ : 2 * Real.pi < V₀) (hV : V₀ < V) :
    0 < deriv (wuSprungX V₀) V := by
  have hV₀_pos : 0 < V₀ := by linarith [Real.pi_pos]
  have hy_gt : 1 < V / V₀ := (one_lt_div hV₀_pos).mpr hV
  have hpi_pos : 0 < Real.pi := Real.pi_pos
  have hlog1 : 0 < Real.log (V₀ / (2 * Real.pi)) :=
    Real.log_pos ((one_lt_div (by positivity)).mpr hV₀)
  have hsqrt_y : 1 < Real.sqrt (V / V₀) := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_lt_sqrt zero_le_one hy_gt
  have hsqrt_y1 : 0 < Real.sqrt (V / V₀ - 1) := Real.sqrt_pos.mpr (by linarith)
  have hlog2 : 0 < Real.log (Real.sqrt (V / V₀) + Real.sqrt (V / V₀ - 1)) :=
    Real.log_pos (by linarith)
  rw [(wuSprungX_hasDerivAt hV₀ hV).deriv]
  positivity

theorem wuSprungX_self (V₀ : ℝ) : wuSprungX V₀ V₀ = 0 := by
  by_cases hV₀ : V₀ = 0
  · subst hV₀; simp [wuSprungX]
  · simp [wuSprungX, wuSprungNormalized, div_self hV₀]

theorem wuSprungX_continuousOn {V₀ : ℝ} (hV₀ : 0 < V₀) :
    ContinuousOn (wuSprungX V₀) (Set.Ici V₀) := by
  have hsub_ne : ∀ V ∈ Set.Ici V₀, Real.sqrt (V / V₀) - Real.sqrt (V / V₀ - 1) ≠ 0 := by
    intro V hV
    have hy : 1 ≤ V / V₀ := (one_le_div hV₀).mpr hV
    exact (sqrt_sub_sqrt_pos hy).ne'
  have hfrac_ne : ∀ V ∈ Set.Ici V₀,
      (Real.sqrt (V / V₀) + Real.sqrt (V / V₀ - 1)) /
        (Real.sqrt (V / V₀) - Real.sqrt (V / V₀ - 1)) ≠ 0 := by
    intro V hV
    have hy : 1 ≤ V / V₀ := (one_le_div hV₀).mpr hV
    have hpos : 0 < Real.sqrt (V / V₀) + Real.sqrt (V / V₀ - 1) := by
      have : 0 < Real.sqrt (V / V₀) := Real.sqrt_pos.mpr (by linarith)
      linarith [Real.sqrt_nonneg (V / V₀ - 1)]
    exact div_ne_zero hpos.ne' (hsub_ne V hV)
  unfold wuSprungX wuSprungNormalized
  refine continuousOn_const.mul (ContinuousOn.add ?_ ?_)
  · exact ((continuous_id.div_const V₀).sub continuous_const).sqrt.continuousOn.mul
      continuousOn_const
  · refine (continuous_id.div_const V₀).sqrt.continuousOn.mul ?_
    refine ContinuousOn.log ?_ hfrac_ne
    refine ContinuousOn.div ?_ ?_ hsub_ne
    · exact ((continuous_id.div_const V₀).sqrt.add
        ((continuous_id.div_const V₀).sub continuous_const).sqrt).continuousOn
    · exact ((continuous_id.div_const V₀).sqrt.sub
        ((continuous_id.div_const V₀).sub continuous_const).sqrt).continuousOn

theorem wuSprungX_strictMonoOn {V₀ : ℝ} (hV₀ : 2 * Real.pi < V₀) :
    StrictMonoOn (wuSprungX V₀) (Set.Ici V₀) := by
  have hV₀_pos : 0 < V₀ := by linarith [Real.pi_pos]
  refine strictMonoOn_of_deriv_pos (convex_Ici V₀) (wuSprungX_continuousOn hV₀_pos) ?_
  intro V hV
  rw [interior_Ici] at hV
  exact wuSprungX_deriv_pos hV₀ hV

theorem wuSprungX_tendsto_atTop {V₀ : ℝ} (hV₀ : 0 < V₀) :
    Filter.Tendsto (wuSprungX V₀) Filter.atTop Filter.atTop := by
  have hpref : 0 < Real.sqrt V₀ / Real.pi := div_pos (Real.sqrt_pos.mpr hV₀) Real.pi_pos
  have hdiv : Filter.Tendsto (fun V : ℝ => V / V₀) Filter.atTop Filter.atTop :=
    tendsto_id.atTop_div_const hV₀
  have hnorm_top : Filter.Tendsto (wuSprungNormalized V₀) Filter.atTop Filter.atTop := by
    have hsqrt_top : Filter.Tendsto Real.sqrt Filter.atTop Filter.atTop := by
      have hsqrt_eq : Real.sqrt = fun y : ℝ => y ^ (1 / 2 : ℝ) := funext Real.sqrt_eq_rpow
      rw [hsqrt_eq]
      exact tendsto_rpow_atTop (by norm_num)
    have hlog_top :
        Filter.Tendsto (fun y : ℝ => 2 * Real.log (Real.sqrt y) - |wuSprungConst V₀|)
          Filter.atTop Filter.atTop :=
      ((Real.tendsto_log_atTop.comp hsqrt_top).const_mul_atTop (by norm_num)).atTop_add
        tendsto_const_nhds
    have hprod_top :
        Filter.Tendsto
          (fun y : ℝ => Real.sqrt y * (2 * Real.log (Real.sqrt y) - |wuSprungConst V₀|))
          Filter.atTop Filter.atTop :=
      hsqrt_top.atTop_mul_atTop₀ hlog_top
    refine tendsto_atTop_mono' Filter.atTop ?_ hprod_top
    filter_upwards [Filter.eventually_ge_atTop (2 : ℝ)] with y hy
    rw [wuSprungNormalized_eq_simplified (by linarith)]
    have hsqrt_nonneg : 0 ≤ Real.sqrt (y - 1) := Real.sqrt_nonneg _
    have hsqrt_le : Real.sqrt (y - 1) ≤ Real.sqrt y := Real.sqrt_le_sqrt (by linarith)
    have hterm1 : -(|wuSprungConst V₀| * Real.sqrt y) ≤ Real.sqrt (y - 1) * wuSprungConst V₀ := by
      have habs : |Real.sqrt (y - 1) * wuSprungConst V₀| ≤ |wuSprungConst V₀| * Real.sqrt y := by
        rw [abs_mul, abs_of_nonneg hsqrt_nonneg, mul_comm]
        exact mul_le_mul_of_nonneg_left hsqrt_le (abs_nonneg _)
      linarith [neg_abs_le (Real.sqrt (y - 1) * wuSprungConst V₀)]
    have hlog_le : Real.log (Real.sqrt y) ≤ Real.log (Real.sqrt y + Real.sqrt (y - 1)) :=
      Real.log_le_log (Real.sqrt_pos.mpr (by linarith)) (by linarith)
    have hterm2 :
        Real.sqrt y * (2 * Real.log (Real.sqrt y)) ≤
          Real.sqrt y * (2 * Real.log (Real.sqrt y + Real.sqrt (y - 1))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hlog_le (by norm_num))
        (Real.sqrt_nonneg y)
    linarith [show Real.sqrt y * (2 * Real.log (Real.sqrt y) - |wuSprungConst V₀|) =
      -(|wuSprungConst V₀| * Real.sqrt y) + Real.sqrt y * (2 * Real.log (Real.sqrt y)) by ring]
  unfold wuSprungX
  exact (hnorm_top.comp hdiv).const_mul_atTop hpref

theorem wuSprungX_image_Ici {V₀ : ℝ} (hV₀ : 2 * Real.pi < V₀) :
    wuSprungX V₀ '' Set.Ici V₀ = Set.Ici 0 := by
  have hV₀_pos : 0 < V₀ := by linarith [Real.pi_pos]
  have himg := (wuSprungX_continuousOn hV₀_pos).image_Ici_of_monotoneOn
    (wuSprungX_strictMonoOn hV₀).monotoneOn (wuSprungX_tendsto_atTop hV₀_pos)
  simpa only [wuSprungX_self] using himg

/-- Order isomorphism `[V₀, ∞) ≃o [0, ∞)` induced by the Wu–Sprung coordinate `x(V)`. -/
def wuSprungOrderIso (V₀ : ℝ) (hV₀ : 2 * Real.pi < V₀) :
    Set.Ici V₀ ≃o Set.Ici (0 : ℝ) :=
  ((wuSprungX_strictMonoOn hV₀).orderIso (wuSprungX V₀) (Set.Ici V₀)).trans
    (Set.orderIsoOfEq _ _ (wuSprungX_image_Ici hV₀))

/-- Inverted smooth Wu–Sprung potential `V_WS(x)` on `ℝ` (even extension of the inverse on `[0, ∞)`). -/
def wuSprungV (V₀ : ℝ) (hV₀ : 2 * Real.pi < V₀) (x : ℝ) : ℝ :=
  if hx : 0 ≤ x then
    ((wuSprungOrderIso V₀ hV₀).symm ⟨x, hx⟩ : ℝ)
  else
    ((wuSprungOrderIso V₀ hV₀).symm ⟨-x, neg_nonneg.mpr (le_of_not_ge hx)⟩ : ℝ)

theorem wuSprungV_even {V₀ : ℝ} (hV₀ : 2 * Real.pi < V₀) (x : ℝ) :
    wuSprungV V₀ hV₀ (-x) = wuSprungV V₀ hV₀ x := by
  unfold wuSprungV
  by_cases hx : 0 ≤ x
  · by_cases hnx : 0 ≤ -x
    · have hx0 : x = 0 := le_antisymm (by linarith) hx
      subst hx0
      simp
    · simp [hx, hnx]
  · have hnx : 0 ≤ -x := by linarith
    simp [hx, hnx]

theorem wuSprungV_ge {V₀ : ℝ} (hV₀ : 2 * Real.pi < V₀) (x : ℝ) :
    V₀ ≤ wuSprungV V₀ hV₀ x := by
  unfold wuSprungV
  split_ifs with hx
  · exact ((wuSprungOrderIso V₀ hV₀).symm ⟨x, hx⟩).prop
  · exact ((wuSprungOrderIso V₀ hV₀).symm ⟨-x, neg_nonneg.mpr (le_of_not_ge hx)⟩).prop

theorem wuSprungX_wuSprungV {V₀ : ℝ} (hV₀ : 2 * Real.pi < V₀) {x : ℝ} (hx : 0 ≤ x) :
    wuSprungX V₀ (wuSprungV V₀ hV₀ x) = x := by
  have hV : wuSprungV V₀ hV₀ x = ((wuSprungOrderIso V₀ hV₀).symm ⟨x, hx⟩ : ℝ) := by
    simp [wuSprungV, hx]
  have happly :
      (wuSprungOrderIso V₀ hV₀ ((wuSprungOrderIso V₀ hV₀).symm ⟨x, hx⟩) : ℝ) = x := by
    rw [OrderIso.apply_symm_apply]
  have hval :
      (wuSprungOrderIso V₀ hV₀ ((wuSprungOrderIso V₀ hV₀).symm ⟨x, hx⟩) : ℝ) =
        wuSprungX V₀ (((wuSprungOrderIso V₀ hV₀).symm ⟨x, hx⟩ : ℝ)) :=
    rfl
  rw [hV, ← hval, happly]

theorem wuSprungV_wuSprungX {V₀ : ℝ} (hV₀ : 2 * Real.pi < V₀) {V : ℝ} (hV : V₀ ≤ V) :
    wuSprungV V₀ hV₀ (wuSprungX V₀ V) = V := by
  have hx : 0 ≤ wuSprungX V₀ V := by
    rw [← wuSprungX_self V₀]
    exact (wuSprungX_strictMonoOn hV₀).monotoneOn Set.self_mem_Ici hV hV
  have h1 :
      wuSprungOrderIso V₀ hV₀ ⟨V, hV⟩ = ⟨wuSprungX V₀ V, hx⟩ :=
    Subtype.ext rfl
  have h2 :
      (wuSprungOrderIso V₀ hV₀).symm ⟨wuSprungX V₀ V, hx⟩ = ⟨V, hV⟩ := by
    rw [← h1, OrderIso.symm_apply_apply]
  simp only [wuSprungV, hx, ↓reduceDIte, h2]

theorem wuSprungV_zero {V₀ : ℝ} (hV₀ : 2 * Real.pi < V₀) :
    wuSprungV V₀ hV₀ 0 = V₀ := by
  simpa only [wuSprungX_self] using wuSprungV_wuSprungX hV₀ le_rfl

/-! ## Section 5: Riemann–Liouville Fractional Operators & `T16` Witnesses (Castro Eqs. 11–12) -/

/-- Left-sided Riemann–Liouville fractional integral `I_L^α F(x)` with finite lower limit `a`
(Castro 2006 §2, Eq. 11). -/
def riemannLiouvilleLeftIntegral (a α : ℝ) (F : ℝ → ℝ) (x : ℝ) : ℝ :=
  (Real.Gamma α)⁻¹ * ∫ t in a..x, (x - t) ^ (α - 1) * F t

/-- Right-sided Riemann–Liouville fractional integral `I_R^α F(x)` with finite upper limit `b`
(Castro 2006 §2, Eq. 12). -/
def riemannLiouvilleRightIntegral (b α : ℝ) (F : ℝ → ℝ) (x : ℝ) : ℝ :=
  (Real.Gamma α)⁻¹ * ∫ t in x..b, (t - x) ^ (α - 1) * F t

/-- Left-sided Riemann–Liouville fractional derivative `D_L^β F(x) = d/dx (I_L^{1-β} F)(x)`
(Castro 2006 §2, Eq. 11). -/
def riemannLiouvilleLeftDeriv (a β : ℝ) (F : ℝ → ℝ) (x : ℝ) : ℝ :=
  deriv (riemannLiouvilleLeftIntegral a (1 - β) F) x

/-- Right-sided Riemann–Liouville fractional derivative `D_R^β F(x) = -d/dx (I_R^{1-β} F)(x)`
(Castro 2006 §2, Eq. 12). -/
def riemannLiouvilleRightDeriv (b β : ℝ) (F : ℝ → ℝ) (x : ℝ) : ℝ :=
  -deriv (riemannLiouvilleRightIntegral b (1 - β) F) x

private theorem intervalIntegrable_sub_rpow {α a x : ℝ} (hα : 0 < α) :
    IntervalIntegrable (fun t : ℝ => (x - t) ^ (α - 1)) volume a x := by
  have hint : IntervalIntegrable (fun u : ℝ => u ^ (α - 1)) volume 0 (x - a) :=
    intervalIntegral.intervalIntegrable_rpow' (by linarith [hα])
  simpa only [sub_sub_cancel, sub_zero] using (hint.comp_sub_left x).symm

private theorem intervalIntegrable_rpow_sub {α x b : ℝ} (hα : 0 < α) :
    IntervalIntegrable (fun t : ℝ => (t - x) ^ (α - 1)) volume x b := by
  have hint : IntervalIntegrable (fun u : ℝ => u ^ (α - 1)) volume 0 (b - x) :=
    intervalIntegral.intervalIntegrable_rpow' (by linarith [hα])
  simpa only [zero_add, sub_add_cancel] using hint.comp_sub_right x

theorem riemannLiouvilleLeftIntegral_intervalIntegrable {a α x : ℝ} (hα : 0 < α)
    {F : ℝ → ℝ} (hF : ContinuousOn F (uIcc a x)) :
    IntervalIntegrable (fun t : ℝ => (x - t) ^ (α - 1) * F t) volume a x :=
  (intervalIntegrable_sub_rpow hα).mul_continuousOn hF

theorem riemannLiouvilleRightIntegral_intervalIntegrable {b α x : ℝ} (hα : 0 < α)
    {F : ℝ → ℝ} (hF : ContinuousOn F (uIcc x b)) :
    IntervalIntegrable (fun t : ℝ => (t - x) ^ (α - 1) * F t) volume x b :=
  (intervalIntegrable_rpow_sub hα).mul_continuousOn hF

theorem riemannLiouvilleLeftIntegral_add {a α x : ℝ} (hα : 0 < α)
    {F G : ℝ → ℝ} (hF : ContinuousOn F (uIcc a x)) (hG : ContinuousOn G (uIcc a x)) :
    riemannLiouvilleLeftIntegral a α (fun t => F t + G t) x =
      riemannLiouvilleLeftIntegral a α F x + riemannLiouvilleLeftIntegral a α G x := by
  unfold riemannLiouvilleLeftIntegral
  have h1 := riemannLiouvilleLeftIntegral_intervalIntegrable hα hF
  have h2 := riemannLiouvilleLeftIntegral_intervalIntegrable hα hG
  simp_rw [mul_add]
  rw [intervalIntegral.integral_add h1 h2, mul_add]

theorem riemannLiouvilleLeftIntegral_smul (a α c : ℝ) (F : ℝ → ℝ) (x : ℝ) :
    riemannLiouvilleLeftIntegral a α (fun t => c * F t) x =
      c * riemannLiouvilleLeftIntegral a α F x := by
  unfold riemannLiouvilleLeftIntegral
  have hrew : (fun t : ℝ => (x - t) ^ (α - 1) * (c * F t)) =
      fun t : ℝ => c * ((x - t) ^ (α - 1) * F t) := by
    ext t; ring
  rw [hrew, intervalIntegral.integral_const_mul, mul_left_comm]

theorem riemannLiouvilleRightIntegral_add {b α x : ℝ} (hα : 0 < α)
    {F G : ℝ → ℝ} (hF : ContinuousOn F (uIcc x b)) (hG : ContinuousOn G (uIcc x b)) :
    riemannLiouvilleRightIntegral b α (fun t => F t + G t) x =
      riemannLiouvilleRightIntegral b α F x + riemannLiouvilleRightIntegral b α G x := by
  unfold riemannLiouvilleRightIntegral
  have h1 := riemannLiouvilleRightIntegral_intervalIntegrable hα hF
  have h2 := riemannLiouvilleRightIntegral_intervalIntegrable hα hG
  simp_rw [mul_add]
  rw [intervalIntegral.integral_add h1 h2, mul_add]

theorem riemannLiouvilleRightIntegral_smul (b α c : ℝ) (F : ℝ → ℝ) (x : ℝ) :
    riemannLiouvilleRightIntegral b α (fun t => c * F t) x =
      c * riemannLiouvilleRightIntegral b α F x := by
  unfold riemannLiouvilleRightIntegral
  have hrew : (fun t : ℝ => (t - x) ^ (α - 1) * (c * F t)) =
      fun t : ℝ => c * ((t - x) ^ (α - 1) * F t) := by
    ext t; ring
  rw [hrew, intervalIntegral.integral_const_mul, mul_left_comm]

theorem riemannLiouvilleLeftDeriv_smul (a β c : ℝ) (F : ℝ → ℝ) (x : ℝ) :
    riemannLiouvilleLeftDeriv a β (fun t => c * F t) x =
      c * riemannLiouvilleLeftDeriv a β F x := by
  unfold riemannLiouvilleLeftDeriv
  have hfun : riemannLiouvilleLeftIntegral a (1 - β) (fun t => c * F t) =
      fun y => c * riemannLiouvilleLeftIntegral a (1 - β) F y :=
    funext fun y => riemannLiouvilleLeftIntegral_smul a (1 - β) c F y
  rw [hfun, deriv_const_mul_field]

theorem riemannLiouvilleLeftDeriv_add {a β x : ℝ} (hβ : β < 1) {F G : ℝ → ℝ}
    (hF : Continuous F) (hG : Continuous G)
    (hdF : DifferentiableAt ℝ (riemannLiouvilleLeftIntegral a (1 - β) F) x)
    (hdG : DifferentiableAt ℝ (riemannLiouvilleLeftIntegral a (1 - β) G) x) :
    riemannLiouvilleLeftDeriv a β (fun t => F t + G t) x =
      riemannLiouvilleLeftDeriv a β F x + riemannLiouvilleLeftDeriv a β G x := by
  unfold riemannLiouvilleLeftDeriv
  have hfun : riemannLiouvilleLeftIntegral a (1 - β) (fun t => F t + G t) =
      fun y => riemannLiouvilleLeftIntegral a (1 - β) F y +
        riemannLiouvilleLeftIntegral a (1 - β) G y :=
    funext fun y =>
      riemannLiouvilleLeftIntegral_add (by linarith [hβ]) hF.continuousOn hG.continuousOn
  rw [hfun]
  exact (hdF.hasDerivAt.add hdG.hasDerivAt).deriv

private theorem intervalIntegrable_rpow_mul_sub_rpow {α β L : ℝ} (hα : 0 < α) (hβ : 0 < β)
    (hL : 0 < L) :
    IntervalIntegrable (fun u : ℝ => u ^ (β - 1) * (L - u) ^ (α - 1)) volume 0 L := by
  have h1 : IntervalIntegrable (fun u : ℝ => u ^ (β - 1) * (L - u) ^ (α - 1)) volume 0 (L / 2) := by
    refine (intervalIntegral.intervalIntegrable_rpow' (by linarith [hβ])).mul_continuousOn ?_
    refine ContinuousOn.rpow_const (by fun_prop) ?_
    intro u hu
    rw [uIcc_of_le (by linarith [hL] : (0 : ℝ) ≤ L / 2)] at hu
    exact Or.inl (ne_of_gt (by linarith [hu.2, hL]))
  have h2 : IntervalIntegrable (fun u : ℝ => u ^ (β - 1) * (L - u) ^ (α - 1)) volume (L / 2) L := by
    have hcont : ContinuousOn (fun u : ℝ => u ^ (β - 1)) (uIcc (L / 2) L) := by
      refine ContinuousOn.rpow_const continuousOn_id ?_
      intro u hu
      rw [uIcc_of_le (by linarith [hL] : L / 2 ≤ L)] at hu
      exact Or.inl (ne_of_gt (by linarith [hu.1, hL]))
    have hint : IntervalIntegrable (fun u : ℝ => (L - u) ^ (α - 1)) volume (L / 2) L :=
      intervalIntegrable_sub_rpow hα
    exact hint.continuousOn_mul hcont
  exact h1.trans h2

private theorem real_betaIntegral_scaled {α β L : ℝ} (hα : 0 < α) (hβ : 0 < β) (hL : 0 < L) :
    ∫ u in 0..L, u ^ (β - 1) * (L - u) ^ (α - 1) =
      L ^ (β + α - 1) * (Real.Gamma β * Real.Gamma α / Real.Gamma (β + α)) := by
  have hc_int :
      (∫ u in 0..L, ((u ^ (β - 1) * (L - u) ^ (α - 1) : ℝ) : ℂ)) =
        ∫ u in 0..L, (u : ℂ) ^ ((β : ℂ) - 1) * ((L : ℂ) - u) ^ ((α : ℂ) - 1) := by
    refine intervalIntegral.integral_congr_ae (ae_of_all _ fun u hu => ?_)
    rw [uIoc_of_le hL.le] at hu
    have hu0 : 0 ≤ u := hu.1.le
    have hLu0 : 0 ≤ L - u := sub_nonneg.mpr hu.2
    rw [Complex.ofReal_mul, Complex.ofReal_cpow hu0, Complex.ofReal_cpow hLu0]
    push_cast
    rfl
  have hscaled := Complex.betaIntegral_scaled (β : ℂ) (α : ℂ) hL
  have hgamma :
      Complex.Gamma (β : ℂ) * Complex.Gamma (α : ℂ) =
        Complex.Gamma ((β : ℂ) + (α : ℂ)) * Complex.betaIntegral (β : ℂ) (α : ℂ) :=
    Complex.Gamma_mul_Gamma_eq_betaIntegral (by simpa using hβ) (by simpa using hα)
  have hgam_sum_pos : 0 < Real.Gamma (β + α) := Real.Gamma_pos_of_pos (by linarith)
  have hgam_sum_ne : Complex.Gamma ((β : ℂ) + (α : ℂ)) ≠ 0 := by
    rw [← Complex.ofReal_add, Complex.Gamma_ofReal]
    exact Complex.ofReal_ne_zero.mpr hgam_sum_pos.ne'
  have hbeta_eq :
      Complex.betaIntegral (β : ℂ) (α : ℂ) =
        ((Real.Gamma β * Real.Gamma α / Real.Gamma (β + α) : ℝ) : ℂ) := by
    have h1 : Complex.betaIntegral (β : ℂ) (α : ℂ) =
        (Complex.Gamma (β : ℂ) * Complex.Gamma (α : ℂ)) / Complex.Gamma ((β : ℂ) + (α : ℂ)) := by
      rw [eq_div_iff hgam_sum_ne, mul_comm, hgamma]
    rw [h1, Complex.Gamma_ofReal, Complex.Gamma_ofReal, ← Complex.ofReal_add, Complex.Gamma_ofReal]
    push_cast
    rfl
  have hpow_eq :
      (L : ℂ) ^ ((β : ℂ) + (α : ℂ) - 1) = ((L ^ (β + α - 1) : ℝ) : ℂ) := by
    rw [Complex.ofReal_cpow hL.le]
    push_cast
    rfl
  have hfull :
      ((∫ u in 0..L, u ^ (β - 1) * (L - u) ^ (α - 1) : ℝ) : ℂ) =
        ((L ^ (β + α - 1) * (Real.Gamma β * Real.Gamma α / Real.Gamma (β + α)) : ℝ) : ℂ) := by
    rw [← intervalIntegral.integral_ofReal, hc_int, hscaled, hbeta_eq, hpow_eq]
    push_cast
    rfl
  exact Complex.ofReal_inj.mp hfull

theorem riemannLiouvilleLeftIntegral_const_one {a α x : ℝ} (hα : 0 < α) :
    riemannLiouvilleLeftIntegral a α (fun _ => (1 : ℝ)) x = (x - a) ^ α / Real.Gamma (α + 1) := by
  unfold riemannLiouvilleLeftIntegral
  simp_rw [mul_one]
  rw [intervalIntegral.integral_comp_sub_left (fun u : ℝ => u ^ (α - 1)) x, sub_self,
    integral_rpow (Or.inl (by linarith [hα])), show α - 1 + 1 = α by ring,
    Real.zero_rpow hα.ne', sub_zero, Real.Gamma_add_one hα.ne']
  have hgam_pos : 0 < Real.Gamma α := Real.Gamma_pos_of_pos hα
  field_simp [hα.ne', hgam_pos.ne']

theorem riemannLiouvilleRightIntegral_const_one {b α x : ℝ} (hα : 0 < α) :
    riemannLiouvilleRightIntegral b α (fun _ => (1 : ℝ)) x = (b - x) ^ α / Real.Gamma (α + 1) := by
  unfold riemannLiouvilleRightIntegral
  simp_rw [mul_one]
  rw [intervalIntegral.integral_comp_sub_right (fun u : ℝ => u ^ (α - 1)) x, sub_self,
    integral_rpow (Or.inl (by linarith [hα])), show α - 1 + 1 = α by ring,
    Real.zero_rpow hα.ne', sub_zero, Real.Gamma_add_one hα.ne']
  have hgam_pos : 0 < Real.Gamma α := Real.Gamma_pos_of_pos hα
  field_simp [hα.ne', hgam_pos.ne']

theorem riemannLiouvilleLeftIntegral_sub_const {a α x : ℝ} (hα : 0 < α) (hax : a ≤ x) :
    riemannLiouvilleLeftIntegral a α (fun t => t - a) x =
      (x - a) ^ (α + 1) / Real.Gamma (α + 2) := by
  unfold riemannLiouvilleLeftIntegral
  have hsub :
      ∫ t in a..x, (x - t) ^ (α - 1) * (t - a) =
        ∫ u in 0..(x - a), u ^ (α - 1) * ((x - a) - u) := by
    have h0 := intervalIntegral.integral_comp_sub_left (a := a) (b := x)
      (fun u => u ^ (α - 1) * ((x - a) - u)) x
    simpa only [sub_self, sub_sub_sub_cancel_left] using h0
  have hint1 : IntervalIntegrable (fun u : ℝ => (x - a) * u ^ (α - 1)) volume 0 (x - a) :=
    (intervalIntegral.intervalIntegrable_rpow' (by linarith [hα])).const_mul _
  have hint2 : IntervalIntegrable (fun u : ℝ => u ^ α) volume 0 (x - a) :=
    intervalIntegral.intervalIntegrable_rpow' (by linarith [hα])
  have hrew :
      ∀ u ∈ uIoc 0 (x - a),
        u ^ (α - 1) * ((x - a) - u) = (x - a) * u ^ (α - 1) - u ^ α := by
    intro u hu
    rw [uIoc_of_le (sub_nonneg.mpr hax)] at hu
    have hu_pos : 0 < u := hu.1
    calc
      u ^ (α - 1) * ((x - a) - u) = (x - a) * u ^ (α - 1) - u ^ (α - 1) * u := by ring
      _ = (x - a) * u ^ (α - 1) - u ^ α := by
        rw [← Real.rpow_add_one hu_pos.ne', show α - 1 + 1 = α by ring]
  rw [hsub, intervalIntegral.integral_congr_ae (ae_of_all _ hrew),
    intervalIntegral.integral_sub hint1 hint2, intervalIntegral.integral_const_mul,
    integral_rpow (Or.inl (by linarith [hα])), integral_rpow (Or.inl (by linarith [hα])),
    show α - 1 + 1 = α by ring, Real.zero_rpow hα.ne',
    Real.zero_rpow (by linarith [hα] : α + 1 ≠ 0)]
  have hxa : (x - a) * (x - a) ^ α = (x - a) ^ (α + 1) := by
    rcases eq_or_lt_of_le hax with rfl | hlt
    · simp [Real.zero_rpow (by linarith [hα] : α + 1 ≠ 0)]
    · rw [mul_comm, ← Real.rpow_add_one (sub_pos.mpr hlt).ne']
  have hgam_pos : 0 < Real.Gamma α := Real.Gamma_pos_of_pos hα
  rw [sub_zero, sub_zero, mul_div_assoc', hxa,
    show Real.Gamma (α + 2) = (α + 1) * α * Real.Gamma α by
      rw [show α + 2 = (α + 1) + 1 by ring, Real.Gamma_add_one (by linarith),
        Real.Gamma_add_one hα.ne']; ring]
  field_simp [hα.ne', (by linarith [hα] : α + 1 ≠ 0), hgam_pos.ne']
  ring

theorem riemannLiouvilleLeftIntegral_rpow_sub {a α γ x : ℝ} (hα : 0 < α) (hγ : -1 < γ)
    (hax : a < x) :
    riemannLiouvilleLeftIntegral a α (fun t => (t - a) ^ γ) x =
      (Real.Gamma (γ + 1) / Real.Gamma (α + γ + 1)) * (x - a) ^ (α + γ) := by
  have hL : 0 < x - a := sub_pos.mpr hax
  unfold riemannLiouvilleLeftIntegral
  have hsub :
      ∫ t in a..x, (x - t) ^ (α - 1) * (t - a) ^ γ =
        ∫ u in 0..(x - a), u ^ ((γ + 1) - 1) * ((x - a) - u) ^ (α - 1) := by
    have hcomp :=
      intervalIntegral.integral_comp_sub_right (a := a) (b := x)
        (fun u : ℝ => ((x - a) - u) ^ (α - 1) * u ^ γ) a
    have hsimp : (fun t : ℝ => ((x - a) - (t - a)) ^ (α - 1) * (t - a) ^ γ) =
        fun t : ℝ => (x - t) ^ (α - 1) * (t - a) ^ γ := by
      ext t; rw [sub_sub_sub_cancel_right]
    rw [hsimp, sub_self] at hcomp
    rw [hcomp]
    refine intervalIntegral.integral_congr fun u _ => ?_
    rw [show γ + 1 - 1 = γ by ring, mul_comm]
  rw [hsub, real_betaIntegral_scaled hα (by linarith [hγ]) hL]
  have hgam_pos : 0 < Real.Gamma α := Real.Gamma_pos_of_pos hα
  rw [show γ + 1 + α - 1 = α + γ by ring, show γ + 1 + α = α + γ + 1 by ring]
  field_simp [hgam_pos.ne']

theorem riemannLiouvilleLeftDeriv_const_one {a β x : ℝ} (hβ : β < 1) (hax : a < x) :
    riemannLiouvilleLeftDeriv a β (fun _ => (1 : ℝ)) x = (x - a) ^ (-β) / Real.Gamma (1 - β) := by
  have hα : 0 < 1 - β := by linarith [hβ]
  have hev :
      riemannLiouvilleLeftIntegral a (1 - β) (fun _ => (1 : ℝ)) =ᶠ[𝓝 x]
        fun y : ℝ => (y - a) ^ (1 - β) / Real.Gamma (2 - β) := by
    filter_upwards with y
    rw [riemannLiouvilleLeftIntegral_const_one hα]
    congr 1
    ring_nf
  have hd_sub : HasDerivAt (fun y : ℝ => y - a) 1 x := (hasDerivAt_id x).sub_const a
  have hd_pow :
      HasDerivAt (fun y : ℝ => (y - a) ^ (1 - β) / Real.Gamma (2 - β))
        (((1 - β) * (x - a) ^ ((1 - β) - 1) * 1) / Real.Gamma (2 - β)) x := by
    convert (hd_sub.rpow_const (p := 1 - β) (Or.inl (sub_pos.mpr hax).ne')).div_const
      (Real.Gamma (2 - β)) using 2
    ring
  have hd := hd_pow.congr_of_eventuallyEq hev
  have hgam_pos : 0 < Real.Gamma (1 - β) := Real.Gamma_pos_of_pos hα
  have hgam2 : Real.Gamma (2 - β) = (1 - β) * Real.Gamma (1 - β) := by
    rw [show 2 - β = (1 - β) + 1 by ring, Real.Gamma_add_one hα.ne']
  unfold riemannLiouvilleLeftDeriv
  rw [hd.deriv, hgam2, show (1 - β) - 1 = -β by ring]
  field_simp [hα.ne', hgam_pos.ne']

theorem riemannLiouvilleRightDeriv_const_one {b β x : ℝ} (hβ : β < 1) (hxb : x < b) :
    riemannLiouvilleRightDeriv b β (fun _ => (1 : ℝ)) x = (b - x) ^ (-β) / Real.Gamma (1 - β) := by
  have hα : 0 < 1 - β := by linarith [hβ]
  have hev :
      riemannLiouvilleRightIntegral b (1 - β) (fun _ => (1 : ℝ)) =ᶠ[𝓝 x]
        fun y : ℝ => (b - y) ^ (1 - β) / Real.Gamma (2 - β) := by
    filter_upwards with y
    rw [riemannLiouvilleRightIntegral_const_one hα]
    congr 1
    ring_nf
  have hd_sub : HasDerivAt (fun y : ℝ => b - y) (-1) x :=
    (hasDerivAt_id x).const_sub b
  have hd_pow :
      HasDerivAt (fun y : ℝ => (b - y) ^ (1 - β) / Real.Gamma (2 - β))
        (((1 - β) * (b - x) ^ ((1 - β) - 1) * (-1)) / Real.Gamma (2 - β)) x := by
    convert (hd_sub.rpow_const (p := 1 - β) (Or.inl (sub_pos.mpr hxb).ne')).div_const
      (Real.Gamma (2 - β)) using 2
    ring
  have hd := hd_pow.congr_of_eventuallyEq hev
  have hgam_pos : 0 < Real.Gamma (1 - β) := Real.Gamma_pos_of_pos hα
  have hgam2 : Real.Gamma (2 - β) = (1 - β) * Real.Gamma (1 - β) := by
    rw [show 2 - β = (1 - β) + 1 by ring, Real.Gamma_add_one hα.ne']
  unfold riemannLiouvilleRightDeriv
  rw [hd.deriv, hgam2, show (1 - β) - 1 = -β by ring]
  field_simp [hα.ne', hgam_pos.ne']

theorem riemannLiouvilleLeftDeriv_sub_const {a β x : ℝ} (hβ : β < 1) (hax : a < x) :
    riemannLiouvilleLeftDeriv a β (fun t => t - a) x =
      (x - a) ^ (1 - β) / Real.Gamma (2 - β) := by
  have hα : 0 < 1 - β := by linarith [hβ]
  have hev :
      riemannLiouvilleLeftIntegral a (1 - β) (fun t => t - a) =ᶠ[𝓝 x]
        fun y : ℝ => (y - a) ^ (2 - β) / Real.Gamma (3 - β) := by
    filter_upwards [Ioi_mem_nhds hax] with y hy
    rw [riemannLiouvilleLeftIntegral_sub_const hα (le_of_lt hy)]
    congr 1 <;> ring_nf
  have hd_sub : HasDerivAt (fun y : ℝ => y - a) 1 x := (hasDerivAt_id x).sub_const a
  have hd_pow :
      HasDerivAt (fun y : ℝ => (y - a) ^ (2 - β) / Real.Gamma (3 - β))
        (((2 - β) * (x - a) ^ ((2 - β) - 1) * 1) / Real.Gamma (3 - β)) x := by
    convert (hd_sub.rpow_const (p := 2 - β) (Or.inl (sub_pos.mpr hax).ne')).div_const
      (Real.Gamma (3 - β)) using 2
    ring
  have hd := hd_pow.congr_of_eventuallyEq hev
  have hgam2_pos : 0 < Real.Gamma (2 - β) := Real.Gamma_pos_of_pos (by linarith)
  have hgam3 : Real.Gamma (3 - β) = (2 - β) * Real.Gamma (2 - β) := by
    rw [show 3 - β = (2 - β) + 1 by ring, Real.Gamma_add_one (by linarith)]
  unfold riemannLiouvilleLeftDeriv
  rw [hd.deriv, hgam3, show (2 - β) - 1 = 1 - β by ring]
  field_simp [(by linarith : 2 - β ≠ 0), hgam2_pos.ne']

theorem riemannLiouvilleLeftDeriv_rpow_sub {a β γ x : ℝ} (hβ : β < 1) (hγ : 0 ≤ γ)
    (hax : a < x) :
    riemannLiouvilleLeftDeriv a β (fun t => (t - a) ^ γ) x =
      (Real.Gamma (γ + 1) / Real.Gamma (γ + 1 - β)) * (x - a) ^ (γ - β) := by
  have hα : 0 < 1 - β := by linarith [hβ]
  have hev :
      riemannLiouvilleLeftIntegral a (1 - β) (fun t => (t - a) ^ γ) =ᶠ[𝓝 x]
        fun y : ℝ => (Real.Gamma (γ + 1) / Real.Gamma (γ + 2 - β)) * (y - a) ^ (1 - β + γ) := by
    filter_upwards [Ioi_mem_nhds hax] with y hy
    rw [riemannLiouvilleLeftIntegral_rpow_sub hα (by linarith [hγ]) hy]
    congr 2
    ring_nf
  have hd_sub : HasDerivAt (fun y : ℝ => y - a) 1 x := (hasDerivAt_id x).sub_const a
  have hd_pow :
      HasDerivAt (fun y : ℝ => (Real.Gamma (γ + 1) / Real.Gamma (γ + 2 - β)) *
          (y - a) ^ (1 - β + γ))
        ((Real.Gamma (γ + 1) / Real.Gamma (γ + 2 - β)) *
          ((1 - β + γ) * (x - a) ^ ((1 - β + γ) - 1) * 1)) x := by
    convert (hd_sub.rpow_const (p := 1 - β + γ) (Or.inl (sub_pos.mpr hax).ne')).const_mul
      (Real.Gamma (γ + 1) / Real.Gamma (γ + 2 - β)) using 2
    ring
  have hd := hd_pow.congr_of_eventuallyEq hev
  have hgam_pos : 0 < Real.Gamma (γ + 1 - β) := Real.Gamma_pos_of_pos (by linarith [hβ, hγ])
  have hgam2 : Real.Gamma (γ + 2 - β) = (γ + 1 - β) * Real.Gamma (γ + 1 - β) := by
    rw [show γ + 2 - β = (γ + 1 - β) + 1 by ring, Real.Gamma_add_one (by linarith)]
  unfold riemannLiouvilleLeftDeriv
  rw [hd.deriv, hgam2, show (1 - β + γ) - 1 = γ - β by ring]
  field_simp [(by linarith : γ + 1 - β ≠ 0), hgam_pos.ne']
  ring

private theorem triangle_kernel_integrableOn {a b α : ℝ} (hα : 0 < α) (hab : a ≤ b)
    {k₁ k₂ : ℝ → ℝ} (hk₁ : IntervalIntegrable (fun s => ‖k₁ s‖) volume a b)
    (hk₁_meas : AEStronglyMeasurable k₁ (volume.restrict (Ioc a b)))
    (hk₂_cont : ContinuousOn k₂ (Set.Icc a b)) :
    IntegrableOn
      (Function.uncurry fun s t : ℝ => if t < s then k₁ s * (s - t) ^ (α - 1) * k₂ t else 0)
      (Ioc a b ×ˢ Ioc a b) := by
  let μ := volume.restrict (Ioc a b)
  let K : ℝ × ℝ → ℝ := fun p => if p.2 < p.1 then k₁ p.1 * (p.1 - p.2) ^ (α - 1) * k₂ p.2 else 0
  have hk₂_meas : AEStronglyMeasurable k₂ μ :=
    (hk₂_cont.mono Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc
  have hpow_meas : Measurable (fun p : ℝ × ℝ => (p.1 - p.2) ^ (α - 1)) :=
    (measurable_fst.sub measurable_snd).pow_const _
  have hbase_meas : AEStronglyMeasurable
      (fun p : ℝ × ℝ => k₁ p.1 * (p.1 - p.2) ^ (α - 1) * k₂ p.2) (μ.prod μ) :=
    ((hk₁_meas.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_fst).mul
      hpow_meas.aestronglyMeasurable).mul
      (hk₂_meas.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_snd)
  have hK_meas : AEStronglyMeasurable K (μ.prod μ) := by
    have hind : K = Set.indicator {p : ℝ × ℝ | p.2 < p.1}
        (fun p : ℝ × ℝ => k₁ p.1 * (p.1 - p.2) ^ (α - 1) * k₂ p.2) := by
      ext p
      simp [K, Set.indicator]
    rw [hind]
    exact hbase_meas.indicator (measurableSet_lt measurable_snd measurable_fst)
  obtain ⟨M₂, hM₂⟩ := isCompact_Icc.exists_bound_of_continuousOn hk₂_cont
  have hM₂_nonneg : 0 ≤ M₂ := by
    have ha := hM₂ a (left_mem_Icc.mpr hab)
    exact (norm_nonneg _).trans ha
  have hK_slice : ∀ᵐ s ∂μ, Integrable (fun t => K (s, t)) μ := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    have has : a ≤ s := hs.1.le
    have hsb : s ≤ b := hs.2
    have hk₂_sub : ContinuousOn k₂ (uIcc a s) := by
      rw [uIcc_of_le has]
      exact hk₂_cont.mono (Icc_subset_Icc_right hsb)
    have hint_s : IntervalIntegrable (fun t => k₁ s * (s - t) ^ (α - 1) * k₂ t) volume a s :=
      ((riemannLiouvilleLeftIntegral_intervalIntegrable hα hk₂_sub).const_mul (k₁ s)).congr
        (fun t _ => by ring)
    have hint_ind : Integrable
        (Set.indicator (Ioc a s) (fun t => k₁ s * (s - t) ^ (α - 1) * k₂ t)) volume :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le has).mp hint_s |>.integrable_indicator
        measurableSet_Ioc
    have hint_μ : Integrable
        (Set.indicator (Ioc a s) (fun t => k₁ s * (s - t) ^ (α - 1) * k₂ t)) μ :=
      hint_ind.mono_measure Measure.restrict_le_self
    refine hint_μ.congr ?_
    have hne : ∀ᵐ t ∂μ, t ≠ s := ae_iff.mpr (by simp)
    filter_upwards [ae_restrict_mem measurableSet_Ioc, hne] with t htm hts
    by_cases hlt : t < s
    · simp [K, hlt, htm.1, hlt.le]
    · have hnot : t ∉ Ioc a s := fun h => hlt (lt_of_le_of_ne h.2 hts)
      simp [K, hlt, Set.indicator_of_notMem hnot]
  have houter_meas : AEStronglyMeasurable (fun s => ∫ t, ‖K (s, t)‖ ∂μ) μ :=
    hK_meas.norm.integral_prod_right'
  have hbound_int : Integrable (fun s => (M₂ * ((b - a) ^ α / α)) * ‖k₁ s‖) μ :=
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mp hk₁).const_mul _
  have houter_le : ∀ᵐ s ∂μ, ‖∫ t, ‖K (s, t)‖ ∂μ‖ ≤ (M₂ * ((b - a) ^ α / α)) * ‖k₁ s‖ := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    have has : a ≤ s := hs.1.le
    have hsb : s ≤ b := hs.2
    have hnn : 0 ≤ ∫ t, ‖K (s, t)‖ ∂μ := integral_nonneg fun _ => norm_nonneg _
    rw [Real.norm_of_nonneg hnn]
    have hsplit :
        (∫ t, ‖K (s, t)‖ ∂μ) =
          ∫ t in Ioc a s, ‖k₁ s‖ * (s - t) ^ (α - 1) * ‖k₂ t‖ := by
      have hsub_set : Ioc a s ⊆ Ioc a b := Ioc_subset_Ioc_right hsb
      have heq_ind :
          (fun t => ‖K (s, t)‖) =ᵐ[μ]
            Set.indicator (Ioc a s) (fun t => ‖k₁ s‖ * (s - t) ^ (α - 1) * ‖k₂ t‖) := by
        have hne : ∀ᵐ t ∂μ, t ≠ s := ae_iff.mpr (by simp)
        filter_upwards [ae_restrict_mem measurableSet_Ioc, hne] with t htm hts
        by_cases hlt : t < s
        · have hpow_nn : 0 ≤ (s - t) ^ (α - 1) := Real.rpow_nonneg (sub_nonneg.mpr hlt.le) _
          simp [K, hlt, htm.1, hlt.le, norm_mul, Real.norm_of_nonneg hpow_nn]
        · have hnot : t ∉ Ioc a s := fun h => hlt (lt_of_le_of_ne h.2 hts)
          simp [K, hlt, Set.indicator_of_notMem hnot]
      rw [integral_congr_ae heq_ind, integral_indicator measurableSet_Ioc]
      simp only [μ, Measure.restrict_restrict measurableSet_Ioc, inter_eq_left.mpr hsub_set]
    rw [hsplit]
    have hk₂_sub : ContinuousOn k₂ (uIcc a s) := by
      rw [uIcc_of_le has]
      exact hk₂_cont.mono (Icc_subset_Icc_right hsb)
    have hint_lhs :
        IntegrableOn (fun t => ‖k₁ s‖ * (s - t) ^ (α - 1) * ‖k₂ t‖) (Ioc a s) := by
      have h1 : IntervalIntegrable (fun t => ‖k₁ s‖ * (s - t) ^ (α - 1) * ‖k₂ t‖) volume a s :=
        (((intervalIntegrable_sub_rpow hα).mul_continuousOn hk₂_sub.norm).const_mul
          ‖k₁ s‖).congr (fun t _ => by ring)
      exact (intervalIntegrable_iff_integrableOn_Ioc_of_le has).mp h1
    have hint_rhs :
        IntegrableOn (fun t => (‖k₁ s‖ * M₂) * (s - t) ^ (α - 1)) (Ioc a s) :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le has).mp
        ((intervalIntegrable_sub_rpow hα).const_mul _)
    have hmono :
        (∫ t in Ioc a s, ‖k₁ s‖ * (s - t) ^ (α - 1) * ‖k₂ t‖) ≤
          ∫ t in Ioc a s, (‖k₁ s‖ * M₂) * (s - t) ^ (α - 1) := by
      refine setIntegral_mono_on hint_lhs hint_rhs measurableSet_Ioc fun t ht => ?_
      have hpow_nn : 0 ≤ (s - t) ^ (α - 1) := Real.rpow_nonneg (sub_nonneg.mpr ht.2) _
      have hk₂_bd : ‖k₂ t‖ ≤ M₂ := hM₂ t ⟨ht.1.le, ht.2.trans hsb⟩
      calc
        ‖k₁ s‖ * (s - t) ^ (α - 1) * ‖k₂ t‖
            ≤ ‖k₁ s‖ * (s - t) ^ (α - 1) * M₂ :=
          mul_le_mul_of_nonneg_left hk₂_bd (mul_nonneg (norm_nonneg _) hpow_nn)
        _ = (‖k₁ s‖ * M₂) * (s - t) ^ (α - 1) := by ring
    have heval :
        (∫ t in Ioc a s, (‖k₁ s‖ * M₂) * (s - t) ^ (α - 1)) =
          (‖k₁ s‖ * M₂) * ((s - a) ^ α / α) := by
      rw [← intervalIntegral.integral_of_le has, intervalIntegral.integral_const_mul,
        intervalIntegral.integral_comp_sub_left (fun u : ℝ => u ^ (α - 1)) s, sub_self,
        integral_rpow (Or.inl (by linarith [hα])), show α - 1 + 1 = α by ring,
        Real.zero_rpow hα.ne', sub_zero]
    have hpow_le : (s - a) ^ α / α ≤ (b - a) ^ α / α :=
      div_le_div_of_nonneg_right
        (Real.rpow_le_rpow (sub_nonneg.mpr has) (by linarith) hα.le) hα.le
    calc
      (∫ t in Ioc a s, ‖k₁ s‖ * (s - t) ^ (α - 1) * ‖k₂ t‖)
          ≤ (‖k₁ s‖ * M₂) * ((s - a) ^ α / α) := hmono.trans_eq heval
      _ ≤ (‖k₁ s‖ * M₂) * ((b - a) ^ α / α) :=
        mul_le_mul_of_nonneg_left hpow_le (mul_nonneg (norm_nonneg _) hM₂_nonneg)
      _ = (M₂ * ((b - a) ^ α / α)) * ‖k₁ s‖ := by ring
  have houter_int : Integrable (fun s => ∫ t, ‖K (s, t)‖ ∂μ) μ :=
    hbound_int.mono' houter_meas houter_le
  rw [IntegrableOn, Measure.volume_eq_prod, ← Measure.prod_restrict]
  change Integrable K (μ.prod μ)
  exact (integrable_prod_iff hK_meas).mpr ⟨hK_slice, houter_int⟩

private theorem intervalIntegral_triangle_split_left {a b : ℝ} (s : ℝ)
    (has : a ≤ s) (hsb : s ≤ b) {g : ℝ → ℝ}
    (hg : IntervalIntegrable g volume a s) :
    (∫ t in a..b, if t < s then g t else 0) = ∫ t in a..s, g t := by
  have h1_ae : ∀ᵐ t ∂volume, t ∈ uIoc a s → (if t < s then g t else 0) = g t := by
    refine ae_iff.mpr (measure_mono_null (fun t ht => ?_) (measure_singleton s))
    by_contra hne
    apply ht
    intro htm
    rw [uIoc_of_le has] at htm
    simp [lt_of_le_of_ne htm.2 hne]
  have h2_ae : ∀ᵐ t ∂volume, t ∈ uIoc s b → (if t < s then g t else 0) = (0 : ℝ) := by
    refine ae_of_all _ fun t ht => ?_
    rw [uIoc_of_le hsb] at ht
    simp [not_lt.mpr ht.1.le]
  have hint1 : IntervalIntegrable (fun t => if t < s then g t else 0) volume a s :=
    hg.congr_ae (EventuallyEq.symm ((ae_restrict_iff' measurableSet_uIoc).mpr h1_ae))
  have hint2 : IntervalIntegrable (fun t => if t < s then g t else 0) volume s b :=
    IntervalIntegrable.congr_ae IntervalIntegrable.zero
      (EventuallyEq.symm ((ae_restrict_iff' measurableSet_uIoc).mpr h2_ae))
  rw [← intervalIntegral.integral_add_adjacent_intervals hint1 hint2,
    intervalIntegral.integral_congr_ae h1_ae,
    intervalIntegral.integral_congr_ae h2_ae, intervalIntegral.integral_zero, add_zero]

private theorem intervalIntegral_triangle_split_right {a b : ℝ} (t : ℝ)
    (hat : a ≤ t) (htb : t ≤ b) {g : ℝ → ℝ}
    (hg : IntervalIntegrable g volume t b) :
    (∫ s in a..b, if t < s then g s else 0) = ∫ s in t..b, g s := by
  have h1_ae : ∀ᵐ s ∂volume, s ∈ uIoc a t → (if t < s then g s else 0) = (0 : ℝ) := by
    refine ae_of_all _ fun s hs => ?_
    rw [uIoc_of_le hat] at hs
    simp [not_lt.mpr hs.2]
  have h2_ae : ∀ᵐ s ∂volume, s ∈ uIoc t b → (if t < s then g s else 0) = g s := by
    refine ae_of_all _ fun s hs => ?_
    rw [uIoc_of_le htb] at hs
    simp [hs.1]
  have hint1 : IntervalIntegrable (fun s => if t < s then g s else 0) volume a t :=
    IntervalIntegrable.congr_ae IntervalIntegrable.zero
      (EventuallyEq.symm ((ae_restrict_iff' measurableSet_uIoc).mpr h1_ae))
  have hint2 : IntervalIntegrable (fun s => if t < s then g s else 0) volume t b :=
    hg.congr_ae (EventuallyEq.symm ((ae_restrict_iff' measurableSet_uIoc).mpr h2_ae))
  rw [← intervalIntegral.integral_add_adjacent_intervals hint1 hint2,
    intervalIntegral.integral_congr_ae h1_ae,
    intervalIntegral.integral_congr_ae h2_ae, intervalIntegral.integral_zero, zero_add]

/-- Left–right integral adjointness on `[a, b]`:
`∫ x in a..b, g x * I_L^α f a x = ∫ t in a..b, I_R^α g b t * f t`. -/
theorem riemannLiouville_left_right_adjoint {a b α : ℝ} (hα : 0 < α) (hab : a ≤ b)
    {f g : ℝ → ℝ} (hf : ContinuousOn f (Set.Icc a b)) (hg : ContinuousOn g (Set.Icc a b)) :
    (∫ x in a..b, g x * riemannLiouvilleLeftIntegral a α f x) =
      ∫ t in a..b, riemannLiouvilleRightIntegral b α g t * f t := by
  let K : ℝ → ℝ → ℝ := fun x t => if t < x then g x * (x - t) ^ (α - 1) * f t else 0
  have hg_uIcc : ContinuousOn g (uIcc a b) := by rwa [uIcc_of_le hab]
  have hk₁ : IntervalIntegrable (fun s => ‖g s‖) volume a b :=
    hg_uIcc.norm.intervalIntegrable
  have hk₁_meas : AEStronglyMeasurable g (volume.restrict (Ioc a b)) :=
    (hg.mono Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc
  have hK_int : IntegrableOn (Function.uncurry K) (Ioc a b ×ˢ Ioc a b) :=
    triangle_kernel_integrableOn hα hab hk₁ hk₁_meas hf
  have hK_int_uIoc : IntegrableOn (Function.uncurry K) (uIoc a b ×ˢ uIoc a b) := by
    simpa only [uIoc_of_le hab] using hK_int
  have hswap := intervalIntegral_intervalIntegral_swap hK_int_uIoc
  have hlhs :
      (∫ x in a..b, g x * riemannLiouvilleLeftIntegral a α f x) =
        (Real.Gamma α)⁻¹ * ∫ x in a..b, ∫ t in a..b, K x t := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr_ae (ae_of_all _ fun x hx => ?_)
    rw [uIoc_of_le hab] at hx
    have hax : a ≤ x := hx.1.le
    have hxb : x ≤ b := hx.2
    have hf_sub : ContinuousOn f (uIcc a x) := by
      rw [uIcc_of_le hax]
      exact hf.mono (Icc_subset_Icc_right hxb)
    have hint_t : IntervalIntegrable (fun t => g x * (x - t) ^ (α - 1) * f t) volume a x :=
      ((riemannLiouvilleLeftIntegral_intervalIntegrable hα hf_sub).const_mul (g x)).congr
        (fun t _ => by ring)
    rw [intervalIntegral_triangle_split_left x hax hxb hint_t]
    unfold riemannLiouvilleLeftIntegral
    have hpull :
        (∫ t in a..x, g x * (x - t) ^ (α - 1) * f t) =
          g x * ∫ t in a..x, (x - t) ^ (α - 1) * f t := by
      simp_rw [mul_assoc]
      exact intervalIntegral.integral_const_mul (g x) _
    rw [hpull]
    ring
  have hrhs :
      (∫ t in a..b, riemannLiouvilleRightIntegral b α g t * f t) =
        (Real.Gamma α)⁻¹ * ∫ t in a..b, ∫ x in a..b, K x t := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr_ae (ae_of_all _ fun t ht => ?_)
    rw [uIoc_of_le hab] at ht
    have hat : a ≤ t := ht.1.le
    have htb : t ≤ b := ht.2
    have hg_sub : ContinuousOn g (uIcc t b) := by
      rw [uIcc_of_le htb]
      exact hg.mono (Icc_subset_Icc_left hat)
    have hint_x : IntervalIntegrable (fun x => g x * (x - t) ^ (α - 1) * f t) volume t b :=
      ((riemannLiouvilleRightIntegral_intervalIntegrable hα hg_sub).mul_const (f t)).congr
        (fun x _ => by ring)
    rw [intervalIntegral_triangle_split_right t hat htb hint_x]
    unfold riemannLiouvilleRightIntegral
    have hpull :
        (∫ x in t..b, g x * (x - t) ^ (α - 1) * f t) =
          (∫ x in t..b, (x - t) ^ (α - 1) * g x) * f t := by
      simp_rw [mul_comm (g _) ((_ - t) ^ (α - 1))]
      exact intervalIntegral.integral_mul_const (f t) (fun x => (x - t) ^ (α - 1) * g x)
    rw [hpull]
    ring
  rw [hlhs, hrhs, hswap]

/-- Semigroup property for left-sided Riemann–Liouville integrals:
`I_L^{α₁} (I_L^{α₂} F) a x = I_L^{α₁ + α₂} F a x`. -/
theorem riemannLiouvilleLeftIntegral_comp {a α₁ α₂ x : ℝ} (hα₁ : 0 < α₁) (hα₂ : 0 < α₂)
    (hax : a ≤ x) {F : ℝ → ℝ} (hF : ContinuousOn F (Set.Icc a x)) :
    riemannLiouvilleLeftIntegral a α₁ (riemannLiouvilleLeftIntegral a α₂ F) x =
      riemannLiouvilleLeftIntegral a (α₁ + α₂) F x := by
  let K : ℝ → ℝ → ℝ :=
    fun s t => if t < s then (x - s) ^ (α₁ - 1) * (s - t) ^ (α₂ - 1) * F t else 0
  have hk₁ : IntervalIntegrable (fun s => ‖(x - s) ^ (α₁ - 1)‖) volume a x :=
    (intervalIntegrable_sub_rpow hα₁).norm
  have hk₁_meas : AEStronglyMeasurable (fun s : ℝ => (x - s) ^ (α₁ - 1))
      (volume.restrict (Ioc a x)) :=
    ((measurable_const.sub measurable_id).pow_const _).aestronglyMeasurable
  have hK_int : IntegrableOn (Function.uncurry K) (Ioc a x ×ˢ Ioc a x) :=
    triangle_kernel_integrableOn hα₂ hax hk₁ hk₁_meas hF
  have hK_int_uIoc : IntegrableOn (Function.uncurry K) (uIoc a x ×ˢ uIoc a x) := by
    simpa only [uIoc_of_le hax] using hK_int
  have hswap := intervalIntegral_intervalIntegral_swap hK_int_uIoc
  have hlhs :
      riemannLiouvilleLeftIntegral a α₁ (riemannLiouvilleLeftIntegral a α₂ F) x =
        (Real.Gamma α₁)⁻¹ * (Real.Gamma α₂)⁻¹ * ∫ s in a..x, ∫ t in a..x, K s t := by
    unfold riemannLiouvilleLeftIntegral
    rw [mul_assoc, ← intervalIntegral.integral_const_mul (Real.Gamma α₂)⁻¹
      (fun s => ∫ t in a..x, K s t)]
    congr 1
    refine intervalIntegral.integral_congr_ae (ae_of_all _ fun s hs => ?_)
    rw [uIoc_of_le hax] at hs
    have has : a ≤ s := hs.1.le
    have hsx : s ≤ x := hs.2
    have hF_sub : ContinuousOn F (uIcc a s) := by
      rw [uIcc_of_le has]
      exact hF.mono (Icc_subset_Icc_right hsx)
    have hint_t :
        IntervalIntegrable (fun t => (x - s) ^ (α₁ - 1) * (s - t) ^ (α₂ - 1) * F t) volume a s :=
      ((riemannLiouvilleLeftIntegral_intervalIntegrable hα₂ hF_sub).const_mul
        ((x - s) ^ (α₁ - 1))).congr (fun t _ => by ring)
    rw [intervalIntegral_triangle_split_left s has hsx hint_t]
    have hpull :
        (∫ t in a..s, (x - s) ^ (α₁ - 1) * (s - t) ^ (α₂ - 1) * F t) =
          (x - s) ^ (α₁ - 1) * ∫ t in a..s, (s - t) ^ (α₂ - 1) * F t := by
      simp_rw [mul_assoc]
      exact intervalIntegral.integral_const_mul ((x - s) ^ (α₁ - 1))
        (fun t => (s - t) ^ (α₂ - 1) * F t)
    rw [hpull]
    ring
  have hrhs :
      (Real.Gamma α₁)⁻¹ * (Real.Gamma α₂)⁻¹ * ∫ t in a..x, ∫ s in a..x, K s t =
        riemannLiouvilleLeftIntegral a (α₁ + α₂) F x := by
    have hgam₁ : 0 < Real.Gamma α₁ := Real.Gamma_pos_of_pos hα₁
    have hgam₂ : 0 < Real.Gamma α₂ := Real.Gamma_pos_of_pos hα₂
    have hgam₁₂ : 0 < Real.Gamma (α₁ + α₂) := Real.Gamma_pos_of_pos (by linarith)
    have hint_eq :
        (∫ t in a..x, ∫ s in a..x, K s t) =
          (Real.Gamma α₁ * Real.Gamma α₂ / Real.Gamma (α₁ + α₂)) *
            ∫ t in a..x, (x - t) ^ (α₁ + α₂ - 1) * F t := by
      rw [← intervalIntegral.integral_const_mul]
      refine intervalIntegral.integral_congr_ae ?_
      refine ae_iff.mpr (measure_mono_null (fun t ht => ?_) (measure_singleton x))
      by_contra htx
      apply ht
      intro htm
      rw [uIoc_of_le hax] at htm
      have hat : a ≤ t := htm.1.le
      have htx_lt : t < x := lt_of_le_of_ne htm.2 htx
      have hL : 0 < x - t := sub_pos.mpr htx_lt
      have hint_s :
          IntervalIntegrable (fun s => (x - s) ^ (α₁ - 1) * (s - t) ^ (α₂ - 1) * F t)
            volume t x := by
        have hcomp :
            IntervalIntegrable (fun u : ℝ => u ^ (α₂ - 1) * (x - t - u) ^ (α₁ - 1))
              volume 0 (x - t) :=
          intervalIntegrable_rpow_mul_sub_rpow hα₁ hα₂ hL
        have hcomp2 :
            IntervalIntegrable
              (fun s : ℝ => (s - t) ^ (α₂ - 1) * (x - t - (s - t)) ^ (α₁ - 1)) volume t x := by
          simpa only [zero_add, sub_add_cancel] using hcomp.comp_sub_right t
        exact (hcomp2.mul_const (F t)).congr (fun s _ => by
          rw [sub_sub_sub_cancel_right, mul_comm ((s - t) ^ (α₂ - 1))])
      rw [intervalIntegral_triangle_split_right t hat htx_lt.le hint_s,
        intervalIntegral.integral_mul_const (F t)
          (fun s => (x - s) ^ (α₁ - 1) * (s - t) ^ (α₂ - 1))]
      have hsub :
          (∫ s in t..x, (x - s) ^ (α₁ - 1) * (s - t) ^ (α₂ - 1)) =
            ∫ u in 0..(x - t), u ^ (α₂ - 1) * ((x - t) - u) ^ (α₁ - 1) := by
        have h0 :=
          intervalIntegral.integral_comp_sub_right (a := t) (b := x)
            (fun u : ℝ => ((x - t) - u) ^ (α₁ - 1) * u ^ (α₂ - 1)) t
        have hrew : (fun s : ℝ => ((x - t) - (s - t)) ^ (α₁ - 1) * (s - t) ^ (α₂ - 1)) =
            fun s : ℝ => (x - s) ^ (α₁ - 1) * (s - t) ^ (α₂ - 1) := by
          ext s; rw [sub_sub_sub_cancel_right]
        rw [hrew, sub_self] at h0
        rw [h0]
        refine intervalIntegral.integral_congr fun u _ => mul_comm _ _
      rw [hsub, real_betaIntegral_scaled hα₁ hα₂ hL, show α₂ + α₁ - 1 = α₁ + α₂ - 1 by ring,
        show α₂ + α₁ = α₁ + α₂ by ring]
      ring
    rw [hint_eq]
    unfold riemannLiouvilleLeftIntegral
    field_simp [hgam₁.ne', hgam₂.ne', hgam₁₂.ne']
  rw [hlhs, hswap, hrhs]

private theorem integral_zero_one_id_mul_leftDeriv_one {β : ℝ} (hβ : β < 1) :
    (∫ x in (0 : ℝ)..1, id x * riemannLiouvilleLeftDeriv 0 β (fun _ => (1 : ℝ)) x) =
      ((2 - β) * Real.Gamma (1 - β))⁻¹ := by
  have hev :
      ∀ x ∈ uIoc (0 : ℝ) 1,
        id x * riemannLiouvilleLeftDeriv 0 β (fun _ => (1 : ℝ)) x =
          (Real.Gamma (1 - β))⁻¹ * x ^ (1 - β) := by
    intro x hx
    rw [uIoc_of_le zero_le_one] at hx
    have hx_pos : 0 < x := hx.1
    rw [id_eq, riemannLiouvilleLeftDeriv_const_one hβ hx_pos, sub_zero, div_eq_mul_inv,
      ← mul_assoc, mul_comm x (x ^ (-β)), ← Real.rpow_add_one hx_pos.ne' (-β),
      show -β + 1 = 1 - β by ring, mul_comm]
  rw [intervalIntegral.integral_congr_ae (ae_of_all _ hev), intervalIntegral.integral_const_mul,
    integral_rpow (Or.inl (by linarith [hβ])), Real.one_rpow, show 1 - β + 1 = 2 - β by ring,
    Real.zero_rpow (by linarith [hβ] : 2 - β ≠ 0), sub_zero, one_div, ← mul_inv, mul_comm (2 - β)]

private theorem integral_zero_one_leftDeriv_id_mul_one {β : ℝ} (hβ : β < 1) :
    (∫ x in (0 : ℝ)..1, riemannLiouvilleLeftDeriv 0 β id x * (1 : ℝ)) =
      ((1 - β) * (2 - β) * Real.Gamma (1 - β))⁻¹ := by
  have hev :
      ∀ x ∈ uIoc (0 : ℝ) 1,
        riemannLiouvilleLeftDeriv 0 β id x * (1 : ℝ) =
          (Real.Gamma (2 - β))⁻¹ * x ^ (1 - β) := by
    intro x hx
    rw [uIoc_of_le zero_le_one] at hx
    have hx_pos : 0 < x := hx.1
    have hid : id = fun t : ℝ => t - 0 := by ext t; simp
    rw [mul_one, hid, riemannLiouvilleLeftDeriv_sub_const hβ hx_pos, sub_zero, div_eq_mul_inv,
      mul_comm]
  have hgam2 : Real.Gamma (2 - β) = (1 - β) * Real.Gamma (1 - β) := by
    rw [show 2 - β = (1 - β) + 1 by ring, Real.Gamma_add_one (by linarith [hβ])]
  rw [intervalIntegral.integral_congr_ae (ae_of_all _ hev), intervalIntegral.integral_const_mul,
    integral_rpow (Or.inl (by linarith [hβ])), Real.one_rpow, show 1 - β + 1 = 2 - β by ring,
    Real.zero_rpow (by linarith [hβ] : 2 - β ≠ 0), sub_zero, hgam2, one_div, ← mul_inv]
  congr 1
  ring

/-- Explicit `T16` non-Hermiticity witness for `D_L^β` on `[0, 1]` with `f = 1`, `g = id`
(Castro 2006 §2, p. 6: the Riemann–Liouville fractional derivative is not Hermitian). -/
theorem riemannLiouvilleLeftDeriv_not_hermitian {β : ℝ} (hβ₀ : 0 < β) (hβ₁ : β < 1) :
    (∫ x in (0 : ℝ)..1, id x * riemannLiouvilleLeftDeriv 0 β (fun _ => (1 : ℝ)) x) ≠
      ∫ x in (0 : ℝ)..1, riemannLiouvilleLeftDeriv 0 β id x * (1 : ℝ) := by
  rw [integral_zero_one_id_mul_leftDeriv_one hβ₁,
    integral_zero_one_leftDeriv_id_mul_one hβ₁]
  have hgam_pos : 0 < Real.Gamma (1 - β) := Real.Gamma_pos_of_pos (by linarith)
  intro heq
  have hden := inv_inj.mp heq
  have hmul : (2 - β) * Real.Gamma (1 - β) * 1 =
      (2 - β) * Real.Gamma (1 - β) * (1 - β) := by
    linarith [show (1 - β) * (2 - β) * Real.Gamma (1 - β) =
      (2 - β) * Real.Gamma (1 - β) * (1 - β) by ring]
  have hcancel : 1 = 1 - β :=
    mul_left_cancel₀ (mul_ne_zero (by linarith) hgam_pos.ne') hmul
  linarith [hβ₀]

/-- Specialization of non-Hermiticity of `D_L^β` to Castro's fractal order `β = 3 / 4` (Eq. 7). -/
theorem riemannLiouvilleLeftDeriv_not_hermitian_three_quarters :
    (∫ x in (0 : ℝ)..1, id x * riemannLiouvilleLeftDeriv 0 (3 / 4) (fun _ => (1 : ℝ)) x) ≠
      ∫ x in (0 : ℝ)..1, riemannLiouvilleLeftDeriv 0 (3 / 4) id x * (1 : ℝ) :=
  riemannLiouvilleLeftDeriv_not_hermitian (by norm_num) (by norm_num)

/-- Explicit `[D_L^β, X] ≠ 0` non-commutativity witness at `a = 0, x = 1` acting on `f = 1`. -/
theorem riemannLiouvilleLeftDeriv_mul_coord_ne {β : ℝ} (hβ₀ : 0 < β) (hβ₁ : β < 1) :
    riemannLiouvilleLeftDeriv 0 β (fun t => t * (1 : ℝ)) 1 ≠
      (1 : ℝ) * riemannLiouvilleLeftDeriv 0 β (fun _ => (1 : ℝ)) 1 := by
  have hsub : (fun t : ℝ => t * (1 : ℝ)) = fun t : ℝ => t - 0 := by ext t; simp
  rw [hsub, riemannLiouvilleLeftDeriv_sub_const hβ₁ zero_lt_one,
    riemannLiouvilleLeftDeriv_const_one hβ₁ zero_lt_one, sub_zero, Real.one_rpow,
    Real.one_rpow, one_mul, one_div, one_div]
  have hgam_pos : 0 < Real.Gamma (1 - β) := Real.Gamma_pos_of_pos (by linarith)
  have hgam2 : Real.Gamma (2 - β) = (1 - β) * Real.Gamma (1 - β) := by
    rw [show 2 - β = (1 - β) + 1 by ring, Real.Gamma_add_one (by linarith)]
  rw [hgam2]
  intro heq
  have hden := inv_inj.mp heq
  have hcancel : (1 - β) * Real.Gamma (1 - β) = 1 * Real.Gamma (1 - β) := by linarith
  have h1 : 1 - β = 1 := mul_right_cancel₀ hgam_pos.ne' hcancel
  linarith [hβ₀]

/-- Non-Hermiticity of the left-sided Riemann–Liouville fractional integral `I_L^α` on `[0, 1]`. -/
theorem riemannLiouvilleLeftIntegral_not_hermitian {α : ℝ} (hα : 0 < α) :
    (∫ x in (0 : ℝ)..1, id x * riemannLiouvilleLeftIntegral 0 α (fun _ => (1 : ℝ)) x) ≠
      ∫ x in (0 : ℝ)..1, riemannLiouvilleLeftIntegral 0 α id x * (1 : ℝ) := by
  have hlhs_ae :
      ∀ x ∈ uIoc (0 : ℝ) 1,
        id x * riemannLiouvilleLeftIntegral 0 α (fun _ => (1 : ℝ)) x =
          (Real.Gamma (α + 1))⁻¹ * x ^ (α + 1) := by
    intro x hx
    rw [uIoc_of_le zero_le_one] at hx
    have hx_pos : 0 < x := hx.1
    rw [id_eq, riemannLiouvilleLeftIntegral_const_one hα, sub_zero, div_eq_mul_inv,
      ← mul_assoc, mul_comm x (x ^ α), ← Real.rpow_add_one hx_pos.ne' α, mul_comm]
  have hrhs_ae :
      ∀ x ∈ uIoc (0 : ℝ) 1,
        riemannLiouvilleLeftIntegral 0 α id x * (1 : ℝ) =
          (Real.Gamma (α + 2))⁻¹ * x ^ (α + 1) := by
    intro x hx
    rw [uIoc_of_le zero_le_one] at hx
    have hid : id = fun t : ℝ => t - 0 := by ext t; simp
    rw [mul_one, hid, riemannLiouvilleLeftIntegral_sub_const hα hx.1.le, sub_zero, div_eq_mul_inv,
      mul_comm]
  have hlhs :
      (∫ x in (0 : ℝ)..1, id x * riemannLiouvilleLeftIntegral 0 α (fun _ => (1 : ℝ)) x) =
        ((α + 2) * Real.Gamma (α + 1))⁻¹ := by
    rw [intervalIntegral.integral_congr_ae (ae_of_all _ hlhs_ae),
      intervalIntegral.integral_const_mul,
      integral_rpow (Or.inl (by linarith [hα])), Real.one_rpow, show α + 1 + 1 = α + 2 by ring,
      Real.zero_rpow (by linarith [hα] : α + 2 ≠ 0), sub_zero, one_div, ← mul_inv,
      mul_comm (α + 2)]
  have hrhs :
      (∫ x in (0 : ℝ)..1, riemannLiouvilleLeftIntegral 0 α id x * (1 : ℝ)) =
        ((α + 1) * (α + 2) * Real.Gamma (α + 1))⁻¹ := by
    have hgam2 : Real.Gamma (α + 2) = (α + 1) * Real.Gamma (α + 1) := by
      rw [show α + 2 = (α + 1) + 1 by ring, Real.Gamma_add_one (by linarith)]
    rw [intervalIntegral.integral_congr_ae (ae_of_all _ hrhs_ae),
      intervalIntegral.integral_const_mul,
      integral_rpow (Or.inl (by linarith [hα])), Real.one_rpow, show α + 1 + 1 = α + 2 by ring,
      Real.zero_rpow (by linarith [hα] : α + 2 ≠ 0), sub_zero, hgam2, one_div, ← mul_inv]
    congr 1
    ring
  rw [hlhs, hrhs]
  have hgam_pos : 0 < Real.Gamma (α + 1) := Real.Gamma_pos_of_pos (by linarith)
  intro heq
  have hden := inv_inj.mp heq
  have hmul : (α + 2) * Real.Gamma (α + 1) * 1 =
      (α + 2) * Real.Gamma (α + 1) * (α + 1) := by
    linarith [show (α + 1) * (α + 2) * Real.Gamma (α + 1) =
      (α + 2) * Real.Gamma (α + 1) * (α + 1) by ring]
  have hcancel : 1 = α + 1 :=
    mul_left_cancel₀ (mul_ne_zero (by linarith) hgam_pos.ne') hmul
  linarith [hα]

end InfoGeometry.Analysis.WeierstrassFractalAndFractionalDeriv
