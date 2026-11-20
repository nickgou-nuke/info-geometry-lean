/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Analysis.CliffordWaveletNativeL2
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Position and frequency uncertainty for Schwartz functions

The domain is the real line with Lebesgue measure. The coefficient space can
be any complex Hilbert space. Position multiplication and differentiation
act on Schwartz space; they are not asserted to be bounded on `L2`.

The Fourier convention is Mathlib's `exp (-2 * π * I * x * ξ)`. Consequently
the product of the position and frequency `L2` norms is at least
`‖f‖₂² / (4 * π)`. Both position and frequency centers are arbitrary real
numbers, and normalization of the signal is not required.
-/

noncomputable section

namespace InfoGeometry.Analysis.SchwartzUncertainty

open MeasureTheory

section Real

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

private theorem real_inner_toL2 (f g : SchwartzMap ℝ H) :
    inner ℝ (f.toLp 2 volume) (g.toLp 2 volume) =
      ∫ x : ℝ, inner ℝ (f x) (g x) := by
  rw [MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [f.coeFn_toLp 2 volume, g.coeFn_toLp 2 volume] with x hf hg
  rw [hf, hg]

private theorem toL2_add (f g : SchwartzMap ℝ H) :
    (f + g).toLp 2 volume = f.toLp 2 volume + g.toLp 2 volume :=
  (SchwartzMap.toLpCLM ℝ H 2 volume).map_add f g

/-- The product rule on Schwartz space: differentiating `(x - a) • f x`
adds one copy of `f` to position multiplication of its derivative. -/
theorem deriv_position (f : SchwartzMap ℝ H) (a : ℝ) :
    SchwartzMap.derivCLM ℝ H
        (SchwartzMap.smulLeftCLM H (fun x : ℝ => x - a) f) =
      f + SchwartzMap.smulLeftCLM H (fun x : ℝ => x - a)
        (SchwartzMap.derivCLM ℝ H f) := by
  have hg : (fun x : ℝ => x - a).HasTemperateGrowth := by fun_prop
  ext x
  simp only [SchwartzMap.derivCLM_apply, add_apply,
    SchwartzMap.smulLeftCLM_apply_apply hg]
  rw [SchwartzMap.smulLeftCLM_apply hg]
  simpa only [Pi.smul_def', one_smul, add_comm] using
    (((hasDerivAt_id x).sub_const a).smul (f.hasDerivAt x)).deriv

/-- Integration by parts identifies the position/derivative pairing exactly.
All boundary and integrability conditions follow from Schwartz regularity. -/
theorem real_inner_position_deriv (f : SchwartzMap ℝ H) (a : ℝ) :
    inner ℝ
        ((SchwartzMap.smulLeftCLM H (fun x : ℝ => x - a) f).toLp 2 volume)
        ((SchwartzMap.derivCLM ℝ H f).toLp 2 volume) =
      -(1 / 2 : ℝ) * ‖f.toLp 2 volume‖ ^ 2 := by
  let q := SchwartzMap.smulLeftCLM H (fun x : ℝ => x - a) f
  let d := SchwartzMap.derivCLM ℝ H f
  have hg : (fun x : ℝ => x - a).HasTemperateGrowth := by fun_prop
  have hmove :
      inner ℝ (f.toLp 2 volume)
          ((SchwartzMap.smulLeftCLM H (fun x : ℝ => x - a) d).toLp 2 volume) =
        inner ℝ (q.toLp 2 volume) (d.toLp 2 volume) := by
    rw [real_inner_toL2, real_inner_toL2]
    apply integral_congr_ae
    filter_upwards [] with x
    simp only [q, SchwartzMap.smulLeftCLM_apply_apply hg,
      real_inner_smul_left, real_inner_smul_right]
  have hibp :
      inner ℝ (f.toLp 2 volume) ((SchwartzMap.derivCLM ℝ H q).toLp 2 volume) =
        -inner ℝ (d.toLp 2 volume) (q.toLp 2 volume) := by
    rw [real_inner_toL2, real_inner_toL2]
    exact SchwartzMap.integral_bilinear_deriv_right_eq_neg_left f q (innerSL ℝ)
  have hderiv : SchwartzMap.derivCLM ℝ H q =
      f + SchwartzMap.smulLeftCLM H (fun x : ℝ => x - a) d :=
    deriv_position f a
  rw [hderiv, toL2_add, inner_add_right, hmove,
    real_inner_self_eq_norm_sq, real_inner_comm (q.toLp 2 volume) (d.toLp 2 volume)] at hibp
  change inner ℝ (q.toLp 2 volume) (d.toLp 2 volume) = _
  linarith

/-- The analytic position/derivative uncertainty inequality on Schwartz
functions, with an arbitrary position center and no normalization premise. -/
theorem norm_sq_le_two_mul_position_mul_deriv (f : SchwartzMap ℝ H) (a : ℝ) :
    ‖f.toLp 2 volume‖ ^ 2 ≤
      2 * ‖(SchwartzMap.smulLeftCLM H (fun x : ℝ => x - a) f).toLp 2 volume‖ *
        ‖(SchwartzMap.derivCLM ℝ H f).toLp 2 volume‖ := by
  have h := real_inner_le_norm
    (-(SchwartzMap.smulLeftCLM H (fun x : ℝ => x - a) f).toLp 2 volume)
    ((SchwartzMap.derivCLM ℝ H f).toLp 2 volume)
  rw [inner_neg_left, norm_neg, real_inner_position_deriv] at h
  nlinarith

end Real

section Complex

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

private theorem toL2_sub (f g : SchwartzMap ℝ H) :
    (f - g).toLp 2 volume = f.toLp 2 volume - g.toLp 2 volume :=
  (SchwartzMap.toLpCLM ℂ H 2 volume).map_sub f g

private theorem toL2_smul (c : ℂ) (f : SchwartzMap ℝ H) :
    (c • f).toLp 2 volume = c • f.toLp 2 volume :=
  (SchwartzMap.toLpCLM ℂ H 2 volume).map_smul c f

/-- A constant imaginary shift of the derivative does not change the real
position pairing. The parameter `b` is a frequency in the `2π` convention. -/
theorem norm_sq_le_two_mul_position_mul_shifted_deriv
    (f : SchwartzMap ℝ H) (a b : ℝ) :
    ‖f.toLp 2 volume‖ ^ 2 ≤
      2 * ‖(SchwartzMap.smulLeftCLM H (fun x : ℝ => x - a) f).toLp 2 volume‖ *
        ‖(SchwartzMap.derivCLM ℝ H f -
          ((2 * (Real.pi : ℂ) * Complex.I) * b) • f).toLp 2 volume‖ := by
  let : InnerProductSpace ℝ H := InnerProductSpace.complexToReal
  let q := SchwartzMap.smulLeftCLM H (fun x : ℝ => x - a) f
  let d := SchwartzMap.derivCLM ℝ H f
  let c : ℂ := (2 * (Real.pi : ℂ) * Complex.I) * b
  have hg : (fun x : ℝ => x - a).HasTemperateGrowth := by fun_prop
  have hzero : inner ℝ (q.toLp 2 volume) ((c • f).toLp 2 volume) = 0 := by
    rw [real_inner_toL2]
    have hpoint (x : ℝ) : inner ℝ (q x) ((c • f) x) = 0 := by
      simp only [q, SchwartzMap.smulLeftCLM_apply_apply hg, smul_apply,
        real_inner_smul_left]
      have hself : inner ℝ (f x) (c • f x) = 0 := by
        change (inner ℂ (f x) (c • f x)).re = 0
        have hc : c.re = 0 := by simp [c]
        simp only [inner_smul_right, Complex.mul_re, hc, inner_self_im,
          zero_mul, mul_zero, sub_zero]
      rw [hself, mul_zero]
    simp_rw [hpoint]
    simp
  have hpair : inner ℝ (q.toLp 2 volume) ((d - c • f).toLp 2 volume) =
      -(1 / 2 : ℝ) * ‖f.toLp 2 volume‖ ^ 2 := by
    rw [toL2_sub, inner_sub_right, hzero, sub_zero]
    exact real_inner_position_deriv f a
  have h := real_inner_le_norm (-(q.toLp 2 volume)) ((d - c • f).toLp 2 volume)
  rw [inner_neg_left, norm_neg, hpair] at h
  change ‖f.toLp 2 volume‖ ^ 2 ≤
    2 * ‖q.toLp 2 volume‖ * ‖(d - c • f).toLp 2 volume‖
  nlinarith

variable [CompleteSpace H]

/-- The Fourier transform of the centered derivative is the centered frequency
multiplier, with the native factor `2 * π * I`. -/
theorem fourier_shifted_deriv (f : SchwartzMap ℝ H) (b : ℝ) :
    FourierTransform.fourier
        (SchwartzMap.derivCLM ℝ H f -
          ((2 * (Real.pi : ℂ) * Complex.I) * b) • f) =
      (2 * (Real.pi : ℂ) * Complex.I) •
        SchwartzMap.smulLeftCLM H (fun ξ : ℝ => ξ - b) (FourierTransform.fourier f) := by
  have hd : SchwartzMap.derivCLM ℝ H f = LineDeriv.lineDerivOp (1 : ℝ) f := by
    ext x
    rw [SchwartzMap.derivCLM_apply, SchwartzMap.lineDerivOp_apply_eq_fderiv,
      fderiv_apply_one_eq_deriv]
  rw [sub_eq_add_neg, FourierTransform.fourier_add, FourierTransform.fourier_neg,
    FourierTransform.fourier_smul, hd,
    CliffordWaveletNativeL2.fourier_lineDeriv_eq_frequencyMultiplication]
  have hg : (fun ξ : ℝ => ξ).HasTemperateGrowth := by fun_prop
  have hg' : (fun ξ : ℝ => ξ - b).HasTemperateGrowth := by fun_prop
  ext ξ
  simp only [add_apply, neg_apply, smul_apply,
    SchwartzMap.smulLeftCLM_apply_apply hg, SchwartzMap.smulLeftCLM_apply_apply hg',
    Real.inner_apply, mul_one]
  rw [← Complex.coe_smul, ← Complex.coe_smul, smul_smul, smul_smul,
    ← neg_smul, ← add_smul]
  congr 1
  push_cast
  ring

/-- Plancherel turns the shifted derivative norm into `2π` times the centered
frequency-moment norm. -/
theorem norm_shifted_deriv_eq_two_pi_mul_frequency
    (f : SchwartzMap ℝ H) (b : ℝ) :
    ‖(SchwartzMap.derivCLM ℝ H f -
        ((2 * (Real.pi : ℂ) * Complex.I) * b) • f).toLp 2 volume‖ =
      (2 * Real.pi) *
        ‖(SchwartzMap.smulLeftCLM H (fun ξ : ℝ => ξ - b)
          (FourierTransform.fourier f)).toLp 2 volume‖ := by
  rw [← CliffordWaveletNativeL2.norm_fourier_toL2_eq,
    fourier_shifted_deriv, toL2_smul, norm_smul]
  simp [Real.norm_eq_abs, abs_of_pos Real.pi_pos]

/-- Position/frequency uncertainty for Hilbert-valued Schwartz functions and
arbitrary real centers. Frequency is measured in cycles per unit coordinate. -/
theorem norm_sq_le_four_pi_mul_position_mul_frequency
    (f : SchwartzMap ℝ H) (a b : ℝ) :
    ‖f.toLp 2 volume‖ ^ 2 ≤
      (4 * Real.pi) *
        ‖(SchwartzMap.smulLeftCLM H (fun x : ℝ => x - a) f).toLp 2 volume‖ *
        ‖(SchwartzMap.smulLeftCLM H (fun ξ : ℝ => ξ - b)
          (FourierTransform.fourier f)).toLp 2 volume‖ := by
  calc
    ‖f.toLp 2 volume‖ ^ 2 ≤
        2 * ‖(SchwartzMap.smulLeftCLM H (fun x : ℝ => x - a) f).toLp 2 volume‖ *
          ‖(SchwartzMap.derivCLM ℝ H f -
            ((2 * (Real.pi : ℂ) * Complex.I) * b) • f).toLp 2 volume‖ :=
      norm_sq_le_two_mul_position_mul_shifted_deriv f a b
    _ = _ := by rw [norm_shifted_deriv_eq_two_pi_mul_frequency]; ring

omit [CompleteSpace H] in
/-- With momentum `P = -I * ħ * d/dx`, the same estimate has the physical
constant `|ħ| / 2`. This is a moment estimate about position `a` and momentum zero. -/
theorem abs_hbar_mul_norm_sq_le_two_mul_position_mul_momentum
    (f : SchwartzMap ℝ H) (a ħ : ℝ) :
    |ħ| * ‖f.toLp 2 volume‖ ^ 2 ≤
      2 * ‖(SchwartzMap.smulLeftCLM H (fun x : ℝ => x - a) f).toLp 2 volume‖ *
        ‖((-Complex.I * (ħ : ℂ)) • (SchwartzMap.derivCLM ℝ H f)).toLp 2 volume‖ := by
  let : InnerProductSpace ℝ H := InnerProductSpace.complexToReal
  have h := mul_le_mul_of_nonneg_left
    (norm_sq_le_two_mul_position_mul_deriv f a) (abs_nonneg ħ)
  rw [toL2_smul, norm_smul]
  have hc : ‖-Complex.I * (ħ : ℂ)‖ = |ħ| := by simp [Real.norm_eq_abs]
  rw [hc]
  nlinarith

end Complex

end InfoGeometry.Analysis.SchwartzUncertainty
