/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Topology.MetricSpace.Bounded

/-!
# InfoGeometry.Analysis.GammaVerticalStripBounds

Ported to Mathlib `v4.34.1` from `mccorvie/riemann-masullo` (Apache-2.0, upstream
commit `b967ac4`):
- `RiemannMasullo/ForMathlib/Analysis/SpecialFunctions/Gamma/Bounds.lean`
- `RiemannMasullo/ForMathlib/Analysis/SpecialFunctions/Gamma/VerticalStrip.lean`

Provides:
- `norm_Gamma_le_real_Gamma`: `‖Complex.Gamma z‖ ≤ Real.Gamma z.re` for `0 < z.re`;
- `exists_norm_inv_Gamma_le_exp_mul_abs_im`: uniform `exp (π * |im z|)` bound on `(Complex.Gamma z)⁻¹` on strips;
- `inv_Gammaℝ_add_isBigO_exp`: `IsBigO` bound for `(Complex.Gammaℝ (s + w))⁻¹`;
- `norm_inv_Gamma_half`: reflection bound on `re w = 1 / 2` with rate `π / 2`;
- `exists_norm_inv_Gamma_le_half_exp_on_strip` and `exists_norm_inv_GammaReal_add_le_on_strip`.
-/

open Filter Function MeasureTheory Set
open scoped Asymptotics Topology ComplexConjugate

namespace InfoGeometry.Analysis.GammaVerticalStripBounds

local notation "atHeight" => comap (abs ∘ Complex.im) atTop

/-- On the right half-plane the norm of Euler's gamma integral is bounded by
the gamma integral at the real part. -/
theorem norm_Gamma_le_real_Gamma {z : ℂ} (hz : 0 < z.re) :
    ‖Complex.Gamma z‖ ≤ Real.Gamma z.re := by
  rw [Complex.Gamma_eq_integral hz, Real.Gamma_eq_integral hz, Complex.GammaIntegral]
  refine (norm_integral_le_integral_norm _).trans_eq (integral_congr_ae ?_)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le,
    Complex.norm_cpow_eq_rpow_re_of_pos hx, Complex.sub_re, Complex.one_re]

/-- On any fixed strip, the reciprocal gamma function is bounded by a constant
times `exp (π * |im z|)` at absolute heights at least one. -/
theorem exists_norm_inv_Gamma_le_exp_mul_abs_im (a b : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℂ, z.re ∈ Icc a b → 1 ≤ |z.im| →
      ‖(Complex.Gamma z)⁻¹‖ ≤ C * Real.exp (Real.pi * |z.im|) := by
  obtain ⟨n, hn⟩ := exists_nat_gt b
  have hCont : ContinuousOn Real.Gamma (Icc (1 - b + n) (1 - a + n)) :=
    Real.differentiableOn_Gamma_Ioi.continuousOn.mono fun x hx ↦
      show 0 < x from lt_of_lt_of_le (by linarith) hx.1
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hCont
  refine ⟨max M 0 / Real.pi, by positivity, fun z hz ht ↦ ?_⟩
  have hShift (w : ℂ) (hw : 1 ≤ |w.im|) (k : ℕ) :
      ‖Complex.Gamma w‖ ≤ ‖Complex.Gamma (w + k)‖ := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Nat.cast_succ, ← add_assoc]
      have hw' : 1 ≤ ‖w + (k : ℂ)‖ :=
        (show 1 ≤ |(w + (k : ℂ)).im| by simpa using hw).trans (Complex.abs_im_le_norm _)
      have hne : w + (k : ℂ) ≠ 0 := norm_pos_iff.mp (zero_lt_one.trans_le hw')
      rw [Complex.Gamma_add_one _ hne, norm_mul]
      exact ih.trans (le_mul_of_one_le_left (norm_nonneg _) hw')
  have hRe : (1 - z + (n : ℂ)).re ∈ Icc (1 - b + n) (1 - a + n) := by
    simp only [Complex.add_re, Complex.sub_re, Complex.one_re, Complex.natCast_re, mem_Icc]
    exact ⟨by linarith [hz.2], by linarith [hz.1]⟩
  have hGamma : ‖Complex.Gamma (1 - z)‖ ≤ max M 0 := by
    refine (hShift (1 - z) (by simpa using ht) n).trans ?_
    refine (norm_Gamma_le_real_Gamma (lt_of_lt_of_le (by linarith) hRe.1)).trans ?_
    exact (le_abs_self _).trans ((hM _ hRe).trans (le_max_left _ _))
  have hSin (w : ℂ) : ‖Complex.sin w‖ ≤ Real.exp |w.im| := by
    have h := norm_sub_le (Complex.exp (-w * Complex.I)) (Complex.exp (w * Complex.I))
    have he := congrArg (fun z : ℂ ↦ ‖z‖) (Complex.two_sin w)
    simp only [norm_mul, Complex.norm_I, mul_one] at he
    norm_num [Complex.norm_exp, Complex.mul_re] at he h
    have h₁ := Real.exp_le_exp.mpr (le_abs_self w.im)
    have h₂ := Real.exp_le_exp.mpr (neg_le_abs w.im)
    linarith
  have him : z.im ≠ 0 := by
    intro he
    norm_num [he] at ht
  have hGne : Complex.Gamma z ≠ 0 := Complex.Gamma_ne_zero fun k he ↦ him (by
    rw [he]
    simp)
  have hSne : Complex.sin ((Real.pi : ℂ) * z) ≠ 0 := by
    rw [Complex.sin_ne_zero_iff]
    intro k he
    have him' := congrArg Complex.im he
    have hprod : Real.pi * z.im = 0 := by
      simpa only [Complex.im_ofReal_mul, ← Complex.ofReal_intCast, ← Complex.ofReal_mul,
        Complex.ofReal_im] using him'
    exact (mul_ne_zero Real.pi_ne_zero him) hprod
  have hReflect : (Complex.Gamma z)⁻¹ =
      Complex.Gamma (1 - z) * Complex.sin ((Real.pi : ℂ) * z) / (Real.pi : ℂ) := by
    apply (eq_div_iff (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)).2
    calc
      _ = (Complex.Gamma z)⁻¹ * ((Complex.Gamma z * Complex.Gamma (1 - z)) *
          Complex.sin ((Real.pi : ℂ) * z)) := by
        rw [Complex.Gamma_mul_Gamma_one_sub, div_mul_cancel₀ _ hSne]
      _ = _ := by rw [← mul_assoc, ← mul_assoc, inv_mul_cancel₀ hGne, one_mul]
  rw [hReflect, norm_div, norm_mul, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le,
    div_mul_eq_mul_div]
  apply div_le_div_of_nonneg_right _ Real.pi_pos.le
  refine mul_le_mul hGamma ?_ (norm_nonneg _) (le_max_right _ _)
  simpa only [Complex.im_ofReal_mul, abs_mul, abs_of_pos Real.pi_pos] using
    hSin ((Real.pi : ℂ) * z)

/-- Shifting a real archimedean gamma factor contributes a constant to its reciprocal
exponential bound on a fixed strip. -/
theorem inv_Gammaℝ_add_isBigO_exp (a b : ℝ) (w : ℂ) :
    (fun s : ℂ ↦ (Complex.Gammaℝ (s + w))⁻¹) =O[atHeight ⊓ 𝓟 (Complex.re ⁻¹' Icc a b)]
      fun s ↦ Real.exp ((Real.pi / 2) * |s.im|) := by
  let A := (a + w.re) / 2
  let B := (b + w.re) / 2
  obtain ⟨C, hC, hΓ⟩ := exists_norm_inv_Gamma_le_exp_mul_abs_im A B
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := A) (b := B)).exists_bound_of_continuousOn
    (f := fun x ↦ Real.pi ^ x)
    (continuous_const.rpow continuous_id fun _ ↦ Or.inl Real.pi_ne_zero).continuousOn
  have hHeight : Tendsto (fun s : ℂ ↦ |s.im|) (atHeight ⊓ 𝓟 (Complex.re ⁻¹' Icc a b)) atTop :=
    tendsto_inf_left tendsto_comap
  have hStrip : ∀ᶠ s : ℂ in atHeight ⊓ 𝓟 (Complex.re ⁻¹' Icc a b), s.re ∈ Icc a b :=
    eventually_inf_principal.mpr (Eventually.of_forall fun _ hs ↦ hs)
  refine Asymptotics.IsBigO.of_bound (max M 0 * C * Real.exp ((Real.pi / 2) * |w.im|)) ?_
  filter_upwards [hStrip, hHeight.eventually_ge_atTop (2 + |w.im|)] with s hs ht
  let z := (s + w) / 2
  have hz : z.re ∈ Icc A B := by
    simp only [z, A, B, Complex.div_ofNat_re, Complex.add_re, mem_Icc]
    exact ⟨by linarith [hs.1], by linarith [hs.2]⟩
  have hiz : |z.im| = |s.im + w.im| / 2 := by
    simp [z, Complex.div_ofNat_im, abs_div]
  have hzLower : 1 ≤ |z.im| := by
    rw [hiz]
    have hTriangle := abs_sub_abs_le_abs_sub s.im (-w.im)
    rw [abs_neg, sub_neg_eq_add] at hTriangle
    linarith
  have hzUpper : |z.im| ≤ (|s.im| + |w.im|) / 2 := by
    rw [hiz]
    exact div_le_div_of_nonneg_right (abs_add_le _ _) (by norm_num)
  rw [Complex.Gammaℝ_def, mul_inv_rev, neg_div, ← Complex.cpow_neg,
    neg_neg, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos,
    Real.norm_of_nonneg (Real.exp_pos _).le]
  change ‖(Complex.Gamma z)⁻¹‖ * Real.pi ^ z.re ≤ _
  calc
    _ ≤ (C * Real.exp (Real.pi * |z.im|)) * max M 0 :=
      mul_le_mul (hΓ z hz hzLower) ((le_abs_self _).trans ((hM _ hz).trans (le_max_left _ _)))
        (Real.rpow_nonneg Real.pi_pos.le _) (by positivity)
    _ ≤ (C * Real.exp ((Real.pi / 2) * (|s.im| + |w.im|))) * max M 0 := by
      refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hC)
        (le_max_right _ _)
      linarith [mul_le_mul_of_nonneg_left hzUpper Real.pi_pos.le]
    _ = _ := by rw [mul_add, Real.exp_add]; ring

/-- Reflection bounds the reciprocal of gamma on the central line `re w = 1 / 2`
with exponential rate `π / 2`. -/
theorem norm_inv_Gamma_half (w : ℂ) (hw : w.re = 1 / 2) :
    ‖(Complex.Gamma w)⁻¹‖ ≤ Real.exp (Real.pi * |w.im| / 2) := by
  have hc : 1 - w = conj w := by apply Complex.ext <;> simp [hw] ; ring
  have he := congrArg (fun t : ℂ ↦ ‖t⁻¹‖) (Complex.Gamma_mul_Gamma_one_sub w)
  simp only [hc, Complex.Gamma_conj, inv_div, norm_div, norm_inv, norm_mul, Complex.norm_conj,
    Complex.norm_of_nonneg Real.pi_pos.le, mul_inv] at he
  have hSin (z : ℂ) : ‖Complex.sin z‖ ≤ Real.exp |z.im| := by
    have h := norm_sub_le (Complex.exp (-z * Complex.I)) (Complex.exp (z * Complex.I))
    have he := congrArg (fun a : ℂ ↦ ‖a‖) (Complex.two_sin z)
    simp only [norm_mul, Complex.norm_I, mul_one] at he
    norm_num [Complex.norm_exp, Complex.mul_re] at he h
    linarith [Real.exp_le_exp.mpr (le_abs_self z.im), Real.exp_le_exp.mpr (neg_le_abs z.im)]
  have h := (div_le_self (norm_nonneg (Complex.sin (Real.pi * w)))
    (by linarith [Real.pi_gt_three] : 1 ≤ Real.pi)).trans (hSin ((Real.pi : ℂ) * w))
  rw [← he, Complex.im_ofReal_mul, abs_mul, abs_of_pos Real.pi_pos] at h
  have he₂ : Real.exp (Real.pi * |w.im|) = Real.exp (Real.pi * |w.im| / 2) ^ 2 := by
    rw [sq, ← Real.exp_add, add_halves]
  rw [he₂] at h
  rw [norm_inv]
  nlinarith [Real.exp_pos (Real.pi * |w.im| / 2)]

/-- In the positive half-plane a Beta integral compares gamma at height `t`
to gamma at the same height on the central line. -/
theorem exists_norm_inv_Gamma_le_half_exp_on_strip (a b : ℝ) (ha : 0 < a) :
    ∃ C > 0, ∀ z : ℂ, z.re ∈ Icc a b →
      ‖(Complex.Gamma z)⁻¹‖ ≤ C * (1 + |z.im|) * Real.exp (Real.pi * |z.im| / 2) := by
  let k (u v : ℂ) (x : ℝ) := (x : ℂ) ^ (u - 1) * (1 - (x : ℂ)) ^ (v - 1)
  let B := ∫ x : ℝ in 0..1, ‖k (1 / 2) (1 / 2) x‖
  have hs : ContinuousOn (fun t : ℝ ↦ (Real.Gamma t)⁻¹) (Icc (a + 1 / 2) (b + 1 / 2)) := by
    have hdom : Icc (a + 1 / 2) (b + 1 / 2) ⊆ Ioi (0 : ℝ) := fun x hx ↦ by
      change 0 < x; linarith [hx.1]
    exact (Real.differentiableOn_Gamma_Ioi.continuousOn.mono hdom).inv₀ fun x hx ↦
      (Real.Gamma_pos_of_pos (hdom hx)).ne'
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hs
  let C := (1 + |b|) * (1 + |B|) * (1 + |M|)
  refine ⟨C, by dsimp [C]; positivity, fun z hz ↦ ?_⟩
  let w : ℂ := ⟨1 / 2, z.im⟩
  let v := z.re + 1 / 2
  have hw : w.re = 1 / 2 := rfl
  have hv : 0 < v := by dsimp [v]; linarith [hz.1]
  have hsum : w + (v : ℂ) = z + 1 := by apply Complex.ext <;> simp [w, v]; ring
  have hβ : ‖Complex.betaIntegral w (v : ℂ)‖ ≤ B := by
    apply (intervalIntegral.norm_integral_le_integral_norm zero_le_one).trans
    apply intervalIntegral.integral_mono_on_of_le_Ioo zero_le_one
      (Complex.betaIntegral_convergent (by change (0 : ℝ) < 1 / 2; norm_num) hv).norm
      (Complex.betaIntegral_convergent (u := (1 / 2 : ℂ)) (v := (1 / 2 : ℂ))
        (by norm_num) (by norm_num)).norm
    intro x hx
    have hy : 0 < 1 - x := sub_pos.mpr hx.2
    simp only [norm_mul, ← Complex.ofReal_one, ← Complex.ofReal_sub,
      Complex.norm_cpow_eq_rpow_re_of_pos hx.1, Complex.norm_cpow_eq_rpow_re_of_pos hy]
    apply mul_le_mul _ _ (Real.rpow_nonneg hy.le _) (Real.rpow_nonneg hx.1.le _)
    · simp [hw]
    · apply Real.rpow_le_rpow_of_exponent_ge hy (by linarith [hx.1])
      simp [v]; linarith [hz.1]
  have he := Complex.Gamma_mul_Gamma_eq_betaIntegral (s := w) (t := (v : ℂ))
    (show 0 < w.re by rw [hw]; norm_num) hv
  rw [hsum, Complex.Gamma_add_one z (show z ≠ 0 from fun h ↦ by
    have h₀ := ha.trans_le hz.1; simp [h] at h₀)] at he
  have hwG : Complex.Gamma w ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by rw [hw]; norm_num)
  have hzG : Complex.Gamma z ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (ha.trans_le hz.1)
  have hvG : Complex.Gamma (v : ℂ) ≠ 0 := Complex.Gamma_ne_zero_of_re_pos hv
  have hquot : (Complex.Gamma z)⁻¹ =
      z * Complex.betaIntegral w v * (Complex.Gamma (v : ℂ))⁻¹ * (Complex.Gamma w)⁻¹ := by
    field_simp [hwG, hzG, hvG]
    linear_combination he
  have hzN : ‖z‖ ≤ (1 + |b|) * (1 + |z.im|) := by
    refine (Complex.norm_le_abs_re_add_abs_im z).trans ?_
    rw [abs_of_pos (ha.trans_le hz.1)]
    nlinarith [hz.2, le_abs_self b, abs_nonneg z.im, mul_nonneg (abs_nonneg b) (abs_nonneg z.im)]
  have hvM : ‖(Complex.Gamma (v : ℂ))⁻¹‖ ≤ 1 + |M| := by
    rw [Complex.Gamma_ofReal, ← Complex.ofReal_inv, Complex.norm_real]
    exact (hM v ⟨by dsimp [v]; linarith [hz.1], by dsimp [v]; linarith [hz.2]⟩).trans
      (by linarith [le_abs_self M])
  rw [hquot, norm_mul, norm_mul, norm_mul]
  calc
    _ ≤ ((1 + |b|) * (1 + |z.im|)) * (1 + |B|) * (1 + |M|) * Real.exp (Real.pi * |z.im| / 2) := by
      gcongr
      · exact hβ.trans (by linarith [le_abs_self B])
      · exact norm_inv_Gamma_half w hw
    _ = _ := by dsimp [C]; ring

/-- A fixed complex shift of the real archimedean factor costs a constant
on a positive strip. The exponential rate is `π / 4` in the original height. -/
theorem exists_norm_inv_GammaReal_add_le_on_strip (a b : ℝ) (ha : 0 < a) (w : ℂ) (hw : 0 ≤ w.re) :
    ∃ C > 0, ∀ s : ℂ, s.re ∈ Icc a b →
      ‖(Complex.Gammaℝ (s + w))⁻¹‖ ≤ C * ((1 + |s.im|) * Real.exp (Real.pi * |s.im| / 4)) := by
  have ha' : 0 < a := ha
  have hw' : 0 ≤ w.re := hw
  let A := (a + w.re) / 2
  let B := (b + w.re) / 2
  obtain ⟨C, hC, hΓ⟩ := exists_norm_inv_Gamma_le_half_exp_on_strip A B
    (by dsimp [A]; linarith [ha', hw'])
  let P := Real.pi ^ B
  refine ⟨C * (1 + |w.im|) * Real.exp (Real.pi * |w.im| / 4) * P, by dsimp [P]; positivity,
    fun s hs ↦ ?_⟩
  let z := (s + w) / 2
  have hz : z.re ∈ Icc A B := by
    simp only [z, A, B, Complex.div_ofNat_re, Complex.add_re]
    exact ⟨by linarith [hs.1], by linarith [hs.2]⟩
  have him : |z.im| ≤ (|s.im| + |w.im|) / 2 := by
    simp only [z, Complex.div_ofNat_im, Complex.add_im, abs_div,
      abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    exact div_le_div_of_nonneg_right (abs_add_le _ _) (by norm_num)
  have hpoly : 1 + |z.im| ≤ (1 + |w.im|) * (1 + |s.im|) := by
    nlinarith [abs_nonneg w.im, abs_nonneg s.im, mul_nonneg (abs_nonneg w.im) (abs_nonneg s.im)]
  have hexp : Real.exp (Real.pi * |z.im| / 2) ≤
      Real.exp (Real.pi * |w.im| / 4) * Real.exp (Real.pi * |s.im| / 4) := by
    rw [← Real.exp_add, Real.exp_le_exp]
    linarith [mul_le_mul_of_nonneg_left him Real.pi_pos.le]
  rw [Complex.Gammaℝ_def, mul_inv_rev, neg_div, ← Complex.cpow_neg, neg_neg,
    norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos]
  change ‖(Complex.Gamma z)⁻¹‖ * Real.pi ^ z.re ≤ _
  calc
    _ ≤ (C * ((1 + |w.im|) * (1 + |s.im|)) *
        (Real.exp (Real.pi * |w.im| / 4) * Real.exp (Real.pi * |s.im| / 4))) * P := by
      refine mul_le_mul ((hΓ z hz).trans ?_) (Real.rpow_le_rpow_of_exponent_le
        (by linarith [Real.pi_gt_three]) hz.2) (Real.rpow_nonneg Real.pi_pos.le _) (by positivity)
      gcongr
    _ = _ := by ring

end InfoGeometry.Analysis.GammaVerticalStripBounds
