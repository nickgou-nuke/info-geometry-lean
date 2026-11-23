/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.MellinTransform
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# InfoGeometry.Analysis.RectangleVerticalCauchyIntegral

Ported to Mathlib `v4.34.1` from `mccorvie/riemann-masullo` (Apache-2.0, upstream
commit `b967ac4`):
- `RiemannMasullo/ForMathlib/Analysis/Complex/RectangleIntegral.lean`
- `RiemannMasullo/ForMathlib/Analysis/Complex/VerticalCauchyIntegral.lean`

Provides:
- `rectangleIntegral`, `rectangleIntegral_eq`, `rectangleIntegral_congr_off_countable`,
  `rectangleIntegral_add`, `rectangleIntegral_finsetSum`, `rectangleIntegral_const_mul`,
  `rectangleIntegral_sub_inv` (`2πi` residue inside a rectangle), and
  `rectangleIntegral_sub_zpow_of_ne` (vanishing for `n ≠ -1`);
- `tendsto_symmetric_cauchy_inv`, `tendsto_dslope_vertical`, `tendsto_horizontal_dslope`,
  `verticalCauchyIntegral_sub_eq`, `hasDerivAt_verticalCauchyIntegral`, and
  `verticalCauchy_lpBound` (`L^p`/`L^q` Hölder bound on vertical Cauchy integrals).
-/

noncomputable section

open Filter Function MeasureTheory Set intervalIntegral
open scoped BigOperators Topology Interval ENNReal

namespace InfoGeometry.Analysis.RectangleVerticalCauchyIntegral

/-- The boundary integral following the bottom and right edges from `z` to `w`,
then the top and left edges from `w` back to `z`. -/
def rectangleIntegral (f : ℂ → ℂ) (z w : ℂ) : ℂ :=
  Complex.wedgeIntegral z w f + Complex.wedgeIntegral w z f

/-- The four oriented edge integrals, with real parameters increasing from the
coordinates of `z` to the coordinates of `w`. -/
theorem rectangleIntegral_eq (f : ℂ → ℂ) (z w : ℂ) :
    rectangleIntegral f z w =
      (∫ x : ℝ in z.re..w.re, f (x + z.im * Complex.I)) -
      (∫ x : ℝ in z.re..w.re, f (x + w.im * Complex.I)) +
      Complex.I * (∫ y : ℝ in z.im..w.im, f (w.re + y * Complex.I)) -
      Complex.I * (∫ y : ℝ in z.im..w.im, f (z.re + y * Complex.I)) := by
  exact Complex.wedgeIntegral_add_wedgeIntegral_eq z w f

private theorem horizontal_mapsTo_boundary {z w : ℂ} {y : ℝ} (hw : z.re ≤ w.re)
    (hy : y = z.im ∨ y = w.im) (ht : z.im ≤ w.im) :
    MapsTo (fun x : ℝ ↦ (x : ℂ) + y * Complex.I) (uIcc z.re w.re)
      ((Icc z.re w.re ×ℂ Icc z.im w.im) \ (Ioo z.re w.re ×ℂ Ioo z.im w.im)) := by
  intro x hx
  rw [uIcc_of_le hw] at hx
  rcases hy with rfl | rfl <;> simp [Complex.mem_reProdIm, hx, ht]

private theorem vertical_mapsTo_boundary {z w : ℂ} {x : ℝ} (ht : z.im ≤ w.im)
    (hx : x = z.re ∨ x = w.re) (hw : z.re ≤ w.re) :
    MapsTo (fun y : ℝ ↦ (x : ℂ) + y * Complex.I) (uIcc z.im w.im)
      ((Icc z.re w.re ×ℂ Icc z.im w.im) \ (Ioo z.re w.re ×ℂ Ioo z.im w.im)) := by
  intro y hy
  rw [uIcc_of_le ht] at hy
  rcases hx with rfl | rfl <;> simp [Complex.mem_reProdIm, hy, hw]

private theorem intervalIntegrable_comp_boundary {z w : ℂ} {a b : ℝ} {p : ℝ → ℂ}
    {f : ℂ → ℂ} (hp : Continuous p)
    (hm : MapsTo p (uIcc a b)
      ((Icc z.re w.re ×ℂ Icc z.im w.im) \ (Ioo z.re w.re ×ℂ Ioo z.im w.im)))
    (hf : ContinuousOn f
      ((Icc z.re w.re ×ℂ Icc z.im w.im) \ (Ioo z.re w.re ×ℂ Ioo z.im w.im))) :
    IntervalIntegrable (fun x ↦ f (p x)) volume a b :=
  (hf.comp hp.continuousOn hm).intervalIntegrable

/-- A rectangle integral is unchanged by modifying the integrand at countably
many boundary points. -/
theorem rectangleIntegral_congr_off_countable {f g : ℂ → ℂ} {z w : ℂ} {E : Set ℂ}
    (hw : z.re ≤ w.re) (ht : z.im ≤ w.im) (hE : E.Countable)
    (he : EqOn f g
      (((Icc z.re w.re ×ℂ Icc z.im w.im) \ (Ioo z.re w.re ×ℂ Ioo z.im w.im)) \ E)) :
    rectangleIntegral f z w = rectangleIntegral g z w := by
  have hEdge {a b : ℝ} {p : ℝ → ℂ} (hp : Function.Injective p)
      (hm : MapsTo p (uIcc a b)
        ((Icc z.re w.re ×ℂ Icc z.im w.im) \ (Ioo z.re w.re ×ℂ Ioo z.im w.im))) :
      (∫ x in a..b, f (p x)) = ∫ x in a..b, g (p x) := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [(hE.preimage hp).ae_notMem volume] with x hx hxab
    exact he ⟨hm (uIoc_subset_uIcc hxab), hx⟩
  have hH (y : ℝ) (hy : y = z.im ∨ y = w.im) :=
    hEdge (fun a b hab ↦ by simpa using congrArg Complex.re hab)
      (horizontal_mapsTo_boundary hw hy ht)
  have hV (x : ℝ) (hx : x = z.re ∨ x = w.re) :=
    hEdge (fun a b hab ↦ by simpa using congrArg Complex.im hab)
      (vertical_mapsTo_boundary ht hx hw)
  simp only [rectangleIntegral_eq, hH _ (Or.inl rfl), hH _ (Or.inr rfl),
    hV _ (Or.inl rfl), hV _ (Or.inr rfl)]

/-- The rectangle integral is additive on functions continuous on the boundary. -/
theorem rectangleIntegral_add {f g : ℂ → ℂ} {z w : ℂ}
    (hw : z.re ≤ w.re) (ht : z.im ≤ w.im)
    (hf : ContinuousOn f
      ((Icc z.re w.re ×ℂ Icc z.im w.im) \ (Ioo z.re w.re ×ℂ Ioo z.im w.im)))
    (hg : ContinuousOn g
      ((Icc z.re w.re ×ℂ Icc z.im w.im) \ (Ioo z.re w.re ×ℂ Ioo z.im w.im))) :
    rectangleIntegral (fun s ↦ f s + g s) z w =
      rectangleIntegral f z w + rectangleIntegral g z w := by
  have hEdge {a b : ℝ} {p : ℝ → ℂ} (hp : Continuous p)
      (hm : MapsTo p (uIcc a b)
        ((Icc z.re w.re ×ℂ Icc z.im w.im) \ (Ioo z.re w.re ×ℂ Ioo z.im w.im))) :=
    intervalIntegral.integral_add (intervalIntegrable_comp_boundary hp hm hf)
      (intervalIntegrable_comp_boundary hp hm hg)
  have hH (y : ℝ) (hy : y = z.im ∨ y = w.im) :=
    hEdge (by fun_prop) (horizontal_mapsTo_boundary hw hy ht)
  have hV (x : ℝ) (hx : x = z.re ∨ x = w.re) :=
    hEdge (by fun_prop) (vertical_mapsTo_boundary ht hx hw)
  simp only [rectangleIntegral_eq, hH _ (Or.inl rfl), hH _ (Or.inr rfl),
    hV _ (Or.inl rfl), hV _ (Or.inr rfl), mul_add]
  abel

/-- The integral of a finite sum of functions continuous on the rectangle
boundary is the sum of their boundary integrals. -/
theorem rectangleIntegral_finsetSum {ι : Type*} {F : ι → ℂ → ℂ} {s : Finset ι} {z w : ℂ}
    (hw : z.re ≤ w.re) (ht : z.im ≤ w.im)
    (hF : ∀ i ∈ s, ContinuousOn (F i)
      ((Icc z.re w.re ×ℂ Icc z.im w.im) \ (Ioo z.re w.re ×ℂ Ioo z.im w.im))) :
    rectangleIntegral (fun x ↦ ∑ i ∈ s, F i x) z w =
      ∑ i ∈ s, rectangleIntegral (F i) z w := by
  have hEdge {a b : ℝ} {p : ℝ → ℂ} (hp : Continuous p)
      (hm : MapsTo p (uIcc a b)
        ((Icc z.re w.re ×ℂ Icc z.im w.im) \ (Ioo z.re w.re ×ℂ Ioo z.im w.im))) :=
    intervalIntegral.integral_finsetSum
      (fun i hi ↦ intervalIntegrable_comp_boundary hp hm (hF i hi))
  have hH (y : ℝ) (hy : y = z.im ∨ y = w.im) :=
    hEdge (by fun_prop) (horizontal_mapsTo_boundary hw hy ht)
  have hV (x : ℝ) (hx : x = z.re ∨ x = w.re) :=
    hEdge (by fun_prop) (vertical_mapsTo_boundary ht hx hw)
  simp only [rectangleIntegral_eq, hH _ (Or.inl rfl), hH _ (Or.inr rfl),
    hV _ (Or.inl rfl), hV _ (Or.inr rfl), Finset.sum_add_distrib, Finset.sum_sub_distrib,
    Finset.mul_sum]

/-- A constant factor can be taken outside the rectangle integral. -/
theorem rectangleIntegral_const_mul (c : ℂ) (f : ℂ → ℂ) (z w : ℂ) :
    rectangleIntegral (fun x ↦ c * f x) z w = c * rectangleIntegral f z w := by
  simp only [rectangleIntegral_eq, intervalIntegral.integral_const_mul]
  ring

private theorem integral_log_deriv {p : ℝ → ℂ} {a b : ℝ} {v : ℂ}
    (hp : ∀ x ∈ uIcc a b, HasDerivAt p v x)
    (hslit : ∀ x ∈ uIcc a b, p x ∈ Complex.slitPlane) :
    (∫ x in a..b, v * (p x)⁻¹) = Complex.log (p b) - Complex.log (p a) := by
  apply integral_eq_sub_of_hasDerivAt
  · intro x hx
    simpa only [div_eq_mul_inv] using (hp x hx).clog_real (hslit x hx)
  · have hc : ContinuousOn p (uIcc a b) := fun x hx ↦
      (hp x hx).continuousAt.continuousWithinAt
    exact (continuousOn_const.mul
      (hc.inv₀ fun x hx ↦ Complex.slitPlane_ne_zero (hslit x hx))).intervalIntegrable

private theorem log_neg_of_im_pos {u : ℂ} (hu : 0 < u.im) :
    Complex.log (-u) = Complex.log u - Real.pi * Complex.I := by
  rw [Complex.log, Complex.log, norm_neg, Complex.arg_neg_eq_arg_sub_pi_of_im_pos hu]
  push_cast
  ring

private theorem log_neg_of_im_neg {u : ℂ} (hu : u.im < 0) :
    Complex.log (-u) = Complex.log u + Real.pi * Complex.I := by
  have h := log_neg_of_im_pos (u := -u) (by simpa using neg_pos.mpr hu)
  rw [neg_neg] at h
  linear_combination -h

private theorem hasDerivAt_horizontal (x y : ℝ) (ρ : ℂ) :
    HasDerivAt (fun t : ℝ ↦ (t : ℂ) + y * Complex.I - ρ) 1 x := by
  simpa using ((Complex.ofRealCLM.hasDerivAt (x := x)).add_const
    ((y : ℂ) * Complex.I)).sub_const ρ

private theorem hasDerivAt_vertical (x y : ℝ) (ρ : ℂ) :
    HasDerivAt (fun t : ℝ ↦ (x : ℂ) + t * Complex.I - ρ) Complex.I y := by
  simpa using (((Complex.ofRealCLM.hasDerivAt (x := y)).mul_const
    Complex.I).const_add (x : ℂ)).sub_const ρ

/-- The boundary integral of the simple Cauchy kernel is `2πi` when the
pole is strictly inside the rectangle. -/
theorem rectangleIntegral_sub_inv {z w ρ : ℂ}
    (hρ : ρ ∈ Ioo z.re w.re ×ℂ Ioo z.im w.im) :
    rectangleIntegral (fun s ↦ (s - ρ)⁻¹) z w = 2 * (Real.pi : ℂ) * Complex.I := by
  let p (x y : ℝ) := (x : ℂ) + y * Complex.I - ρ
  have hB := integral_log_deriv (a := z.re) (b := w.re)
    (p := fun x ↦ p x z.im) (fun x _ ↦ hasDerivAt_horizontal x z.im ρ)
    (fun x _ ↦ Complex.mem_slitPlane_iff.mpr
      (Or.inr (by simpa [p] using (sub_neg.mpr hρ.2.1).ne)))
  have hT := integral_log_deriv (a := z.re) (b := w.re)
    (p := fun x ↦ p x w.im) (fun x _ ↦ hasDerivAt_horizontal x w.im ρ)
    (fun x _ ↦ Complex.mem_slitPlane_iff.mpr
      (Or.inr (by simpa [p] using (sub_pos.mpr hρ.2.2).ne')))
  have hR := integral_log_deriv (a := z.im) (b := w.im)
    (p := p w.re) (fun y _ ↦ hasDerivAt_vertical w.re y ρ)
    (fun y _ ↦ Complex.mem_slitPlane_iff.mpr
      (Or.inl (by simpa [p] using sub_pos.mpr hρ.1.2)))
  have hL := integral_log_deriv (a := z.im) (b := w.im)
    (p := fun y ↦ -p z.re y) (fun y _ ↦ (hasDerivAt_vertical z.re y ρ).neg)
    (fun y _ ↦ Complex.mem_slitPlane_iff.mpr
      (Or.inl (by simpa [p] using neg_pos.mpr (sub_neg.mpr hρ.1.1))))
  have hBL : (p z.re z.im).im < 0 := by simpa [p] using sub_neg.mpr hρ.2.1
  have hTL : 0 < (p z.re w.im).im := by simpa [p] using sub_pos.mpr hρ.2.2
  simp only [one_mul] at hB hT
  simp only [inv_neg, neg_mul_neg] at hL
  rw [intervalIntegral.integral_const_mul] at hL hR
  rw [rectangleIntegral_eq]
  change (∫ x in z.re..w.re, (p x z.im)⁻¹) - (∫ x in z.re..w.re, (p x w.im)⁻¹) +
    Complex.I * (∫ y in z.im..w.im, (p w.re y)⁻¹) -
    Complex.I * (∫ y in z.im..w.im, (p z.re y)⁻¹) = _
  rw [hB, hT, hR, hL, log_neg_of_im_pos hTL, log_neg_of_im_neg hBL]
  ring

private theorem integral_zpow_deriv {p : ℝ → ℂ} {a b : ℝ} {v : ℂ} {n : ℤ}
    (hp : ∀ x ∈ uIcc a b, HasDerivAt p v x)
    (hne : ∀ x ∈ uIcc a b, p x ≠ 0) (hn : n ≠ -1) :
    (∫ x in a..b, v * (p x) ^ n) = (p b ^ (n + 1) - p a ^ (n + 1)) / (↑(n + 1) : ℂ) := by
  have hnz : n + 1 ≠ 0 := by
    intro hzero
    apply hn
    omega
  have hcast : (↑(n + 1) : ℂ) ≠ 0 := by
    exact_mod_cast hnz
  rw [sub_div]
  refine integral_eq_sub_of_hasDerivAt
    (f := fun t : ℝ ↦ p t ^ (n + 1) / (↑(n + 1) : ℂ)) ?_ ?_
  · intro x hx
    have hd := (((hasDerivAt_zpow (n + 1) (p x) (Or.inl (hne x hx))).comp x
      (hp x hx)).div_const (↑(n + 1) : ℂ))
    have he : v * p x ^ n = ↑(n + 1) * p x ^ (n + 1 - 1) * v / (↑(n + 1) : ℂ) := by
      rw [add_sub_cancel_right]
      field_simp
    exact he ▸ hd
  · have hc : ContinuousOn p (uIcc a b) := fun x hx ↦
      (hp x hx).continuousAt.continuousWithinAt
    exact (continuousOn_const.mul (hc.zpow₀ n fun x hx ↦ Or.inl (hne x hx))).intervalIntegrable

/-- All integer powers of the Cauchy kernel other than exponent `-1` have a
primitive off the pole and integrate to zero on the rectangle boundary. -/
theorem rectangleIntegral_sub_zpow_of_ne {z w ρ : ℂ} {n : ℤ}
    (hρ : ρ ∈ Ioo z.re w.re ×ℂ Ioo z.im w.im) (hn : n ≠ -1) :
    rectangleIntegral (fun s ↦ (s - ρ) ^ n) z w = 0 := by
  let p (x y : ℝ) := (x : ℂ) + y * Complex.I - ρ
  have hH (y : ℝ) (hy : y ≠ ρ.im) := integral_zpow_deriv (a := z.re) (b := w.re)
    (p := fun x ↦ p x y) (fun x _ ↦ hasDerivAt_horizontal x y ρ)
    (fun x _ he ↦ hy (sub_eq_zero.mp (by simpa [p] using congrArg Complex.im he))) hn
  have hV (x : ℝ) (hx : x ≠ ρ.re) := integral_zpow_deriv (a := z.im) (b := w.im)
    (p := p x) (fun y _ ↦ hasDerivAt_vertical x y ρ)
    (fun y _ he ↦ hx (sub_eq_zero.mp (by simpa [p] using congrArg Complex.re he))) hn
  simp only [one_mul] at hH
  simp only [intervalIntegral.integral_const_mul] at hV
  rw [rectangleIntegral_eq]
  change (∫ x in z.re..w.re, (p x z.im) ^ n) - (∫ x in z.re..w.re, (p x w.im) ^ n) +
    Complex.I * (∫ y in z.im..w.im, (p w.re y) ^ n) -
    Complex.I * (∫ y in z.im..w.im, (p z.re y) ^ n) = _
  rw [hH z.im hρ.2.1.ne, hH w.im hρ.2.2.ne', hV w.re hρ.1.2.ne', hV z.re hρ.1.1.ne]
  ring

local notation "verticalPoint" => (fun (x y : ℝ) ↦ (x : ℂ) + y * Complex.I)

/-- The symmetric truncations of the elementary Cauchy kernel on a vertical line. -/
theorem tendsto_symmetric_cauchy_inv {d : ℝ} (hd : d ≠ 0) :
    Tendsto (fun T : ℝ ↦ ∫ y in -T..T, (verticalPoint d y)⁻¹) atTop
      (𝓝 ((d⁻¹ * (Real.pi / |d⁻¹|) : ℝ) : ℂ)) := by
  let G (y : ℝ) := (verticalPoint d y)⁻¹
  let H (y : ℝ) := d⁻¹ * (1 + (d⁻¹ * y) ^ 2)⁻¹
  have hG : Continuous G := by
    apply Continuous.inv₀ (by dsimp only; fun_prop)
    intro y h
    exact hd (by simpa using congrArg Complex.re h)
  have hH : Integrable H := (integrable_inv_one_add_mul_sq (inv_ne_zero hd)).const_mul _
  have pair (y : ℝ) : G y + G (-y) = 2 * (H y : ℂ) := by
    have hpos : 0 < d * d + y * y := by nlinarith [sq_pos_of_ne_zero hd, sq_nonneg y]
    rw [← Complex.ofReal_ofNat (n := 2), ← Complex.ofReal_mul]
    apply Complex.ext
    · simp only [Complex.add_re, Complex.inv_re, Complex.normSq_apply, Complex.add_im,
        Complex.ofReal_im, Complex.mul_I_re, Complex.mul_I_im, Complex.ofReal_re, neg_zero,
        zero_add, add_zero, neg_mul_neg, G]
      dsimp only [H]
      field_simp [hd]
      ring
    · simp [G, Complex.inv_im, Complex.normSq_apply, neg_div]
  have eq (T : ℝ) : (∫ y in -T..T, G y) = ↑(∫ y in -T..T, H y) := by
    have reflected : (∫ y in -T..T, G (-y)) = ∫ y in -T..T, G y := by
      simp only [intervalIntegral.integral_comp_neg, neg_neg]
    have hadd := intervalIntegral.integral_add (μ := volume)
      (hG.intervalIntegrable (-T) T) ((hG.comp continuous_neg).intervalIntegrable (-T) T)
    simp_rw [Function.comp_apply, pair] at hadd
    rw [reflected, intervalIntegral.integral_const_mul, intervalIntegral.integral_ofReal] at hadd
    linear_combination -hadd / 2
  have lim := intervalIntegral_tendsto_integral hH tendsto_neg_atTop_atBot
    (tendsto_id : Tendsto id atTop (atTop : Filter ℝ))
  have val : (∫ y, H y) = d⁻¹ * (Real.pi / |d⁻¹|) := by
    simp only [H, MeasureTheory.integral_const_mul, integral_univ_inv_one_add_mul_sq]
  rw [← val]
  exact (Complex.continuous_ofReal.continuousAt.tendsto.comp lim).congr fun T ↦ (eq T).symm

/-- Removing the pole subtracts its explicit principal value on each vertical side. -/
theorem tendsto_dslope_vertical {Φ : ℂ → ℂ} {z : ℂ} {σ : ℝ} (hz : σ ≠ z.re)
    (hi : Complex.VerticalIntegrable (fun w ↦ Φ w / (w - z)) σ) :
    Tendsto (fun T : ℝ ↦ ∫ y in -T + z.im..T + z.im, dslope Φ z (verticalPoint σ y)) atTop
      (𝓝 ((∫ y : ℝ, Φ (verticalPoint σ y) / (verticalPoint σ y - z)) -
        Φ z * (if z.re < σ then (Real.pi : ℂ) else -(Real.pi : ℂ)))) := by
  let d := σ - z.re
  have hd : d ≠ 0 := sub_ne_zero.mpr hz
  have hne (y : ℝ) : verticalPoint σ y ≠ z := fun h ↦ hz (by simpa using congrArg Complex.re h)
  have hcont : Continuous (fun y : ℝ ↦ (verticalPoint σ y - z)⁻¹) := by
    exact Continuous.inv₀ (by fun_prop) fun y ↦ sub_ne_zero.mpr (hne y)
  have tr (T : ℝ) : (∫ y in -T + z.im..T + z.im, (verticalPoint σ y - z)⁻¹) =
      ∫ y in -T..T, (verticalPoint d y)⁻¹ := by
    rw [← intervalIntegral.integral_comp_add_right (fun y : ℝ ↦ (verticalPoint σ y - z)⁻¹) z.im]
    apply intervalIntegral.integral_congr
    intro y _
    apply congrArg Inv.inv
    apply Complex.ext <;> simp [d]
  have hval : ((d⁻¹ * (Real.pi / |d⁻¹|) : ℝ) : ℂ) =
      (if z.re < σ then (Real.pi : ℂ) else -(Real.pi : ℂ)) := by
    split_ifs with h
    · have hdpos : 0 < d := sub_pos.mpr h
      rw [abs_of_pos (inv_pos.mpr hdpos)]
      apply congrArg Complex.ofReal
      field_simp [hd]
    · have hdneg : d < 0 := sub_neg.mpr (lt_of_le_of_ne (le_of_not_gt h) hz)
      rw [abs_of_neg (inv_lt_zero.mpr hdneg), ← Complex.ofReal_neg]
      apply congrArg Complex.ofReal
      field_simp [hd]
  have lim := tendsto_symmetric_cauchy_inv hd
  rw [hval] at lim
  have ht : Tendsto (fun T : ℝ ↦ T + z.im) atTop atTop := tendsto_atTop_add_const_right _ _ tendsto_id
  have hb : Tendsto (fun T : ℝ ↦ -T + z.im) atTop atBot :=
    tendsto_atBot_add_const_right _ _ tendsto_neg_atTop_atBot
  have hK := intervalIntegral_tendsto_integral hi hb ht
  apply (hK.sub (lim.const_mul (Φ z))).congr
  intro T
  rw [← tr, ← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_sub]
  · apply intervalIntegral.integral_congr
    intro y _
    dsimp only
    rw [dslope_of_ne _ (hne y), slope_def_field, sub_div, div_eq_mul_inv (Φ z)]
  · exact hi.intervalIntegrable
  · exact (continuous_const.mul hcont).intervalIntegrable _ _

/-- Uniform decay on the strip makes the two horizontal sides of the divided difference vanish. -/
theorem tendsto_horizontal_dslope {Φ : ℂ → ℂ} {z : ℂ} {c d C : ℝ} (hcd : c ≤ d) (hC : 0 ≤ C)
    (hΦ : ∀ᶠ y : ℝ in comap abs atTop, ∀ x ∈ Icc c d, ‖Φ (verticalPoint x y)‖ ≤ C / |y|) :
    Tendsto (fun y : ℝ ↦ ∫ x in c..d, dslope Φ z (verticalPoint x y)) (comap abs atTop) (𝓝 0) := by
  have hy : Tendsto (abs : ℝ → ℝ) (comap abs atTop) atTop := tendsto_comap
  apply squeeze_zero_norm'
  · filter_upwards [hΦ, hy.eventually (eventually_ge_atTop (2 * |z.im| + 1))] with y hφ hlarge
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro x hx
    have hpos : 0 < |y| / 2 := by linarith [abs_nonneg z.im]
    have im := Complex.abs_im_le_norm (verticalPoint x y - z)
    simp only [Complex.sub_im, Complex.add_im, Complex.ofReal_im, Complex.mul_I_im,
      Complex.ofReal_re, zero_add] at im
    have hsep : |y| / 2 ≤ ‖verticalPoint x y - z‖ := by linarith [abs_sub_abs_le_abs_sub y z.im]
    have hne := sub_ne_zero.mp (norm_pos_iff.mp (hpos.trans_le hsep))
    have hnum := (hφ x (Ioc_subset_Icc_self ((uIoc_of_le hcd) ▸ hx))).trans
      (div_le_self hC (by linarith [abs_nonneg z.im]))
    rw [dslope_of_ne _ hne, slope_def_field, norm_div]
    calc ‖Φ (verticalPoint x y) - Φ z‖ / ‖verticalPoint x y - z‖
      _ ≤ (C + ‖Φ z‖) / (|y| / 2) := div_le_div₀ (by positivity)
        ((norm_sub_le _ _).trans (add_le_add hnum le_rfl)) hpos hsep
      _ = (2 * (C + ‖Φ z‖)) / |y| := by ring
  · simpa using ((tendsto_const_nhds (x := 2 * (C + ‖Φ z‖))).div_atTop hy).mul_const |d - c|

/-- The residue of the simple Cauchy kernel between two vertical sides. -/
theorem verticalCauchyIntegral_sub_eq {Φ : ℂ → ℂ} {z : ℂ} {a b c d C : ℝ}
    (hΦ : DifferentiableOn ℂ Φ (Complex.re ⁻¹' Ioo a b)) (ha : a < c) (hb : d < b)
    (hz : z.re ∈ Ioo c d) (hC : 0 ≤ C)
    (hΦdecay : ∀ᶠ y : ℝ in comap abs atTop, ∀ x ∈ Icc c d, ‖Φ (verticalPoint x y)‖ ≤ C / |y|)
    (hc : Complex.VerticalIntegrable (fun w ↦ Φ w / (w - z)) c)
    (hd : Complex.VerticalIntegrable (fun w ↦ Φ w / (w - z)) d) :
    (∫ y : ℝ, Φ (verticalPoint d y) / (verticalPoint d y - z)) -
      (∫ y : ℝ, Φ (verticalPoint c y) / (verticalPoint c y - z)) =
      2 * (Real.pi : ℂ) * Φ z := by
  have hcd := (hz.1.trans hz.2).le
  have hzmem : Complex.re ⁻¹' Ioo a b ∈ 𝓝 z :=
    (isOpen_Ioo.preimage Complex.continuous_re).mem_nhds ⟨ha.trans hz.1, hz.2.trans hb⟩
  have hD := (Complex.differentiableOn_dslope hzmem).mpr hΦ
  let bot (t : ℝ) := -t + z.im
  let top (t : ℝ) := t + z.im
  have hrect (t : ℝ) :
      (∫ x in c..d, dslope Φ z (verticalPoint x (bot t))) -
      (∫ x in c..d, dslope Φ z (verticalPoint x (top t))) +
      Complex.I • (∫ y in bot t..top t, dslope Φ z (verticalPoint d y)) -
      Complex.I • (∫ y in bot t..top t, dslope Φ z (verticalPoint c y)) = 0 := by
    apply Complex.integral_boundary_rect_eq_zero_of_differentiableOn _ (⟨c, bot t⟩ : ℂ) (⟨d, top t⟩ : ℂ)
    apply hD.mono
    intro w hw
    exact Icc_subset_Ioo ha hb ((uIcc_of_le hcd) ▸ hw.1)
  have ht : Tendsto top atTop atTop := tendsto_atTop_add_const_right _ _ tendsto_id
  have hn : Tendsto bot atTop atBot := tendsto_atBot_add_const_right _ _ tendsto_neg_atTop_atBot
  have horiz := tendsto_horizontal_dslope (z := z) hcd hC hΦdecay
  have ht' := horiz.comp (tendsto_comap_iff.mpr (tendsto_abs_atTop_atTop.comp ht))
  have hn' := horiz.comp (tendsto_comap_iff.mpr (tendsto_abs_atBot_atTop.comp hn))
  have vd := tendsto_dslope_vertical hz.2.ne' hd
  have vc := tendsto_dslope_vertical hz.1.ne hc
  rw [ite_eq_left hz.2] at vd
  rw [ite_eq_right (not_lt.mpr hz.1.le)] at vc
  have hlim := (((hn'.sub ht').add (vd.const_smul Complex.I)).sub (vc.const_smul Complex.I))
  have eq := tendsto_nhds_unique hlim (tendsto_const_nhds.congr fun t ↦ (hrect t).symm)
  simp only [sub_zero, zero_add, smul_eq_mul] at eq
  apply mul_left_cancel₀ Complex.I_ne_zero
  linear_combination eq

/-- Differentiating the Cauchy integral in the pole raises the denominator power by one. -/
theorem hasDerivAt_verticalCauchyIntegral {Φ : ℂ → ℂ} {z : ℂ} {σ : ℝ} (hz : z.re ≠ σ)
    (hΦ : Complex.VerticalIntegrable Φ σ) (n : ℕ)
    (hK : Complex.VerticalIntegrable (fun s ↦ Φ s / (s - z) ^ (n + 1)) σ) :
    HasDerivAt (fun w ↦ ∫ y : ℝ, Φ (verticalPoint σ y) / (verticalPoint σ y - w) ^ (n + 1))
      ((n + 1 : ℂ) * ∫ y : ℝ, Φ (verticalPoint σ y) / (verticalPoint σ y - z) ^ (n + 2)) z := by
  let δ := |σ - z.re| / 2
  have hδ : 0 < δ := half_pos (abs_pos.mpr (sub_ne_zero.mpr hz.symm))
  let U := {w : ℂ | δ < |σ - w.re|}
  have hU : U ∈ 𝓝 z := (isOpen_lt continuous_const (continuous_const.sub Complex.continuous_re).abs).mem_nhds
    (show δ < |σ - z.re| by dsimp [δ]; linarith [abs_pos.mpr (sub_ne_zero.mpr hz.symm)])
  have hsep {w : ℂ} (hw : w ∈ U) (y : ℝ) : δ ≤ ‖verticalPoint σ y - w‖ :=
    le_trans (le_of_lt (show δ < |σ - w.re| from hw))
      (by simpa using Complex.abs_re_le_norm (verticalPoint σ y - w))
  let K (m : ℕ) (w : ℂ) (y : ℝ) := Φ (verticalPoint σ y) / (verticalPoint σ y - w) ^ m
  have hmeas : AEStronglyMeasurable (fun y : ℝ ↦ Φ (verticalPoint σ y)) volume := hΦ.aestronglyMeasurable
  have hm (m : ℕ) (w : ℂ) : AEStronglyMeasurable (K m w) volume := by
    have hc : Continuous (fun y : ℝ ↦ (verticalPoint σ y - w) ^ m) := by fun_prop
    change AEStronglyMeasurable (fun y : ℝ ↦ Φ (verticalPoint σ y) / (verticalPoint σ y - w) ^ m) volume
    exact (hmeas.aemeasurable.div hc.measurable.aemeasurable).aestronglyMeasurable
  let A := ‖(n + 1 : ℂ)‖ / δ ^ (n + 2)
  rw [← MeasureTheory.integral_const_mul]
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (F := K (n + 1))
    (F' := fun w y ↦ (n + 1 : ℂ) * K (n + 2) w y)
    (bound := fun y ↦ A * ‖Φ (verticalPoint σ y)‖) hU (Eventually.of_forall (hm _)) hK
    ((hm _ _).const_mul _) ?_ (hΦ.norm.const_mul _) ?_).2
  · filter_upwards with y w hw
    change ‖(n + 1 : ℂ) * (Φ (verticalPoint σ y) / (verticalPoint σ y - w) ^ (n + 2))‖ ≤ _
    rw [norm_mul, norm_div, norm_pow]
    calc ‖(n + 1 : ℂ)‖ * (‖Φ (verticalPoint σ y)‖ / ‖verticalPoint σ y - w‖ ^ (n + 2))
      _ ≤ ‖(n + 1 : ℂ)‖ * (‖Φ (verticalPoint σ y)‖ / δ ^ (n + 2)) := by
        gcongr
        exact hsep hw y
      _ = A * ‖Φ (verticalPoint σ y)‖ := by dsimp [A]; ring
  · filter_upwards with y w hw
    have hne := norm_pos_iff.mp (hδ.trans_le (hsep hw y))
    have hder := (hasDerivAt_const w (Φ (verticalPoint σ y))).div
      (((hasDerivAt_id w).const_sub (verticalPoint σ y)).pow (n + 1)) (pow_ne_zero _ hne)
    convert hder using 1
    · funext x
      rfl
    · dsimp [K]
      push_cast
      field_simp [hne]
      ring

local notation "envelope" => (fun y : ℝ ↦ (1 + ‖y‖)⁻¹)

/-- The translated Cauchy kernel has uniformly bounded conjugate-exponent norm away
from the line. Hölder's inequality then bounds each simple Cauchy integral. -/
theorem verticalCauchy_lpBound (p q : ℝ≥0∞) [ENNReal.HolderTriple p q 1]
    (hq : 1 < q) (hq' : q < ⊤) {δ : ℝ} (hδ : 0 < δ) :
    ∃ C ≥ (0 : ℝ), ∀ {σ : ℝ} {z : ℂ}, δ ≤ |σ - z.re| → ∀ {f : ℝ → ℂ}, MemLp f p volume →
      Integrable (fun y : ℝ ↦ f y / (verticalPoint σ y - z)) ∧
      ‖∫ y : ℝ, f y / (verticalPoint σ y - z)‖ ≤ C * lpNorm f p volume := by
  have hmodel : MemLp envelope q volume := by
    apply (integrable_norm_rpow_iff (by fun_prop) (zero_lt_one.trans hq).ne' hq'.ne).mp
    have hdim : 1 < q.toReal := by
      simpa using (ENNReal.toReal_lt_toReal ENNReal.one_ne_top hq'.ne).2 hq
    have he (x : ℝ) : ‖(1 + ‖x‖)⁻¹‖ = (1 + ‖x‖)⁻¹ := Real.norm_of_nonneg (by positivity)
    simpa only [he, Real.rpow_neg_eq_inv_rpow] using
      (integrable_one_add_norm (μ := (volume : Measure ℝ)) (r := q.toReal) (by simpa using hdim))
  let A := δ⁻¹ + 1
  have hA : 0 ≤ A := by dsimp [A]; positivity
  refine ⟨A * lpNorm envelope q volume, mul_nonneg hA lpNorm_nonneg, ?_⟩
  intro σ z hσ f hf
  let K (y : ℝ) := (verticalPoint σ y - z)⁻¹
  let g := envelope ∘ (fun y : ℝ ↦ y + -z.im)
  have mp := measurePreserving_add_right (volume : Measure ℝ) (-z.im)
  have hg : MemLp g q volume := hmodel.comp_measurePreserving mp
  have sep (y : ℝ) : δ ≤ ‖verticalPoint σ y - z‖ :=
    hσ.trans (by simpa using Complex.abs_re_le_norm (verticalPoint σ y - z))
  have hK : Continuous K := by
    apply Continuous.inv₀ (by fun_prop) fun y ↦ norm_pos_iff.mp (hδ.trans_le (sep y))
  have bound (y : ℝ) : ‖K y‖ ≤ A * ‖g y‖ := by
    have him : |y - z.im| ≤ ‖verticalPoint σ y - z‖ := by
      simpa using Complex.abs_im_le_norm (verticalPoint σ y - z)
    have hy : 0 < ‖verticalPoint σ y - z‖ := hδ.trans_le (sep y)
    have hinv : 1 ≤ δ⁻¹ * ‖verticalPoint σ y - z‖ := (one_le_inv_mul₀ hδ).mpr (sep y)
    change ‖(verticalPoint σ y - z)⁻¹‖ ≤ A * ‖(1 + ‖y + -z.im‖)⁻¹‖
    rw [norm_inv, Real.norm_of_nonneg (by positivity), ← div_eq_mul_inv, inv_eq_one_div,
      div_le_div_iff₀ hy (by positivity)]
    dsimp [A]
    rw [← sub_eq_add_neg]
    linarith
  have hk : MemLp K q volume := hg.of_le_mul (c := A) hK.aestronglyMeasurable (.of_forall bound)
  have hprod : MemLp (f • K) 1 volume := hf.smul hk
  have eq : (fun y : ℝ ↦ f y / (verticalPoint σ y - z)) = f • K := by ext; rfl
  rw [eq]
  refine ⟨memLp_one_iff_integrable.mp hprod, ?_⟩
  have hqeq : eLpNorm g q volume = eLpNorm envelope q volume :=
    eLpNorm_comp_measurePreserving hmodel.aestronglyMeasurable mp
  have hk' := eLpNorm_le_mul_eLpNorm_of_ae_le_mul (μ := volume) hK.aestronglyMeasurable (.of_forall bound) q
  rw [hqeq] at hk'
  have key : lpNorm K q volume ≤ A * lpNorm envelope q volume := by
    simpa only [← toReal_eLpNorm, ENNReal.toReal_mul, ENNReal.toReal_ofReal hA] using
      ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hmodel.eLpNorm_ne_top) hk'
  calc ‖∫ y, (f • K) y‖ ≤ ∫ y, ‖(f • K) y‖ := norm_integral_le_integral_norm _
    _ = lpNorm (f • K) 1 volume := (lpNorm_one_eq_integral_norm hprod.aestronglyMeasurable).symm
    _ ≤ lpNorm f p volume * lpNorm K q volume := by
      simpa only [← toReal_eLpNorm, ENNReal.toReal_mul] using ENNReal.toReal_mono
        (ENNReal.mul_ne_top hf.eLpNorm_ne_top hk.eLpNorm_ne_top)
        (eLpNorm_smul_le_mul_eLpNorm (p := p) (q := q) (r := 1) hf.aestronglyMeasurable hk.aestronglyMeasurable)
    _ ≤ _ := by rw [mul_comm (lpNorm f p volume)]; exact mul_le_mul_of_nonneg_right key lpNorm_nonneg

end InfoGeometry.Analysis.RectangleVerticalCauchyIntegral
