/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
/-
Portions adapted from `external_refs/riemann-masullo`
(`RiemannMasullo/ForMathlib/Analysis/Fourier/PoissonSummation.lean` and
`RiemannMasullo/ForMathlib/Analysis/MellinTransform.lean`, Apache-2.0,
revision `be5d4cb0356d48406eae83233d73c99085b9a038`).
-/
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Fourier.PoissonSummation
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.MellinTransform
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Schwartz Periodization Smoothness & Logarithmic Mellin Convergence

Ports `schwartz_contDiff_periodization`, `isBigO_comp_log_rpow_of_isBigO_exp`,
and `mellinConvergent_of_integrable_logWeight` from `RiemannMasullo` against the
pinned Mathlib `v4.34.1` toolchain.
-/

public section

noncomputable section

namespace InfoGeometry.Analysis.SchwartzPeriodizationMellinConvergence

open Filter MeasureTheory
open scoped Asymptotics ContDiff FourierTransform SchwartzMap

/-- The periodization of a Schwartz function over the integer lattice is smooth. -/
theorem schwartz_contDiff_periodization (f : 𝓢(ℝ, ℂ)) :
    ContDiff ℝ ∞ (fun x : ℝ ↦ ∑' n : ℤ, f (x + n)) := by
  let a (u : ℝ) : ℂ := 2 * Real.pi * Complex.I * u
  let b (k : ℕ) (n : ℤ) := a n ^ k * (𝓕 f) n
  let t (n : ℤ) (x : ℝ) := (𝓕 f) n * fourier n (x : AddCircle (1 : ℝ))
  have hd (n : ℤ) (k : ℕ) :
      iteratedDeriv k (t n) = fun x : ℝ ↦ b k n * fourier n (x : AddCircle (1 : ℝ)) := by
    induction k with
    | zero => simp [b, t]
    | succ k ih =>
      rw [iteratedDeriv_succ, ih]
      funext x
      convert ((hasDerivAt_fourier 1 n x).const_mul (b k n)).deriv using 1
      simp [b, a, pow_succ]
      ring
  have hb (k : ℕ) : Summable fun n : ℤ ↦ ‖b k n‖ := by
    have hg : (fun u : ℝ ↦ a u ^ k).HasTemperateGrowth := by
      dsimp [a]
      fun_prop
    let F := SchwartzMap.smulLeftCLM ℂ (fun u : ℝ ↦ a u ^ k) (𝓕 f)
    have hs : Summable (fun n : ℤ ↦ ‖F n‖) :=
      summable_of_isBigO (Real.summable_abs_int_rpow one_lt_two)
        ((F.isBigO_cocompact_rpow (-2)).norm_left.comp_tendsto Int.tendsto_coe_cofinite)
    simpa only [F, b, SchwartzMap.smulLeftCLM_apply_apply hg, smul_eq_mul] using hs
  simp_rw [f.tsum_eq_tsum_fourier]
  apply contDiff_tsum (f := t) (v := fun k n ↦ ‖b k n‖)
  · intro n
    have hcoe : ContDiff ℝ ∞ ((↑) : ℝ → ℂ) := Complex.ofRealCLM.contDiff
    simp only [t, fourier_coe_apply]
    fun_prop
  · exact fun k _ ↦ hb k
  · intro k n x _
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, hd, norm_mul]
    simp only [fourier_apply, Circle.norm_coe, mul_one, le_rfl]

/-- An exponential growth bound becomes a real-power bound after composition with `log`. -/
theorem isBigO_comp_log_rpow_of_isBigO_exp {g : ℝ → ℂ} {c : ℝ} {l L : Filter ℝ}
    (h : g =O[l] (fun x ↦ Real.exp (c * x)))
    (ht : Tendsto Real.log L l) (hpos : ∀ᶠ t in L, 0 < t) :
    (fun t ↦ g (Real.log t)) =O[L] (fun t ↦ t ^ c) := by
  apply (h.comp_tendsto ht).congr' EventuallyEq.rfl
  filter_upwards [hpos] with t ht
  simp only [Function.comp_apply, Real.rpow_def_of_pos ht, mul_comm]

/-- A logarithmic profile has an absolutely convergent Mellin integral at `s` if its
exponential weight at the real part of `s` is integrable on the real line. -/
theorem mellinConvergent_of_integrable_logWeight (f : ℝ → ℂ) (s : ℂ)
    (h : Integrable (fun x : ℝ ↦ (Real.exp (s.re * x) : ℂ) * f x)) :
    MellinConvergent (fun t ↦ f (Real.log t)) s := by
  let phase (x : ℝ) := Complex.exp ((x : ℂ) * (s - s.re))
  have hc : Continuous phase := by
    dsimp [phase]
    fun_prop
  have hunit (x : ℝ) : ‖phase x‖ ≤ 1 := by
    simp [phase, Complex.norm_exp, Complex.mul_re]
  apply (integrable_comp_exp _).mp
  apply (h.bdd_mul hc.aestronglyMeasurable (Eventually.of_forall hunit)).congr
  filter_upwards with x
  simp only [Real.log_exp, Complex.real_smul, smul_eq_mul]
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast (Real.exp_pos x).ne'),
    ← Complex.ofReal_log (Real.exp_pos x).le, Real.log_exp]
  simp only [phase, Complex.ofReal_exp, Complex.ofReal_mul, ← mul_assoc, ← Complex.exp_add]
  congr 2
  ring

end InfoGeometry.Analysis.SchwartzPeriodizationMellinConvergence

end noncomputable section
