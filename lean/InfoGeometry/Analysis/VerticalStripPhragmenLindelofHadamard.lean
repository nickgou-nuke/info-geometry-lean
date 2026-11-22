/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
/-
Portions adapted from `external_refs/riemann-masullo`
(`RiemannMasullo/ForMathlib/Analysis/Complex/PhragmenLindelof.lean` and
`RiemannMasullo/ForMathlib/Analysis/Complex/Hadamard.lean`, Apache-2.0,
revision `be5d4cb0356d48406eae83233d73c99085b9a038`).
-/
import Mathlib.Analysis.Complex.PhragmenLindelof
import Mathlib.Analysis.Complex.Hadamard

/-!
# Phragmén–Lindelöf & Hadamard Three-Lines Growth Bounds on Vertical Strips

Ports `norm_pow_mul_le_on_verticalStrip`, `norm_le_rpow_on_closedStrip`,
`isBigO_rpow_verticalStrip_interpolate`, and `isBigO_pow_verticalStrip_of_exp` from
`RiemannMasullo` against the pinned Mathlib `v4.34.1` toolchain.
-/

public section

noncomputable section

namespace InfoGeometry.Analysis.VerticalStripPhragmenLindelofHadamard

open Filter Function Set Topology
open scoped Asymptotics

local notation "atHeight" => comap (abs ∘ Complex.im) atTop

/-- A bounded holomorphic function with polynomially weighted bounds on the two edges
of a vertical strip satisfies the same weighted bound throughout the strip. -/
theorem norm_pow_mul_le_on_verticalStrip {a b : ℝ} (hab : a < b) {F : ℂ → ℂ}
    (hF : DiffContOnCl ℂ F (Complex.re ⁻¹' Ioo a b)) {M : ℝ}
    (hM : ∀ z : ℂ, z.re ∈ Icc a b → ‖F z‖ ≤ M) (n : ℕ) {C : ℝ}
    (ha : ∀ z : ℂ, z.re = a → ‖z ^ n * F z‖ ≤ C)
    (hb : ∀ z : ℂ, z.re = b → ‖z ^ n * F z‖ ≤ C)
    (z : ℂ) (hz : z.re ∈ Icc a b) : ‖z ^ n * F z‖ ≤ C := by
  let c := Real.pi / (b - a) / 2
  have hc : 0 < c := by dsimp [c]; positivity
  have hd : DiffContOnCl ℂ (fun w : ℂ ↦ w ^ n * F w) (Complex.re ⁻¹' Ioo a b) :=
    ⟨(differentiableOn_id.pow n).mul hF.1, (continuousOn_id.pow n).mul hF.2⟩
  apply PhragmenLindelof.vertical_strip hd _ ha hb hz.1 hz.2
  refine ⟨c, half_lt_self (div_pos Real.pi_pos (sub_pos.mpr hab)), 1, ?_⟩
  let R := |a| + |b|
  apply Asymptotics.IsBigO.of_bound (M * (n.factorial / c ^ n) * Real.exp (c * R))
  rw [eventually_inf_principal]
  apply Eventually.of_forall
  intro w hw
  have hRe : |w.re| ≤ R := by
    change a < w.re ∧ w.re < b at hw
    dsimp [R]
    exact abs_le.mpr ⟨by linarith [neg_abs_le a, abs_nonneg b],
      by linarith [le_abs_self b, abs_nonneg a]⟩
  have hn : ‖w‖ ^ n ≤ (n.factorial / c ^ n) * Real.exp (c * ‖w‖) := by
    have h := Real.pow_div_factorial_le_exp _ (mul_nonneg hc.le (norm_nonneg w)) n
    rw [mul_pow, div_le_iff₀ (by positivity)] at h
    rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
    linarith only [h]
  have he : Real.exp (c * ‖w‖) ≤ Real.exp (c * R) * Real.exp (c * |w.im|) := by
    rw [← Real.exp_add, ← mul_add]
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left
      ((Complex.norm_le_abs_re_add_abs_im w).trans (add_le_add hRe le_rfl)) hc.le)
  have hM0 := (norm_nonneg (F w)).trans (hM w ⟨hw.1.le, hw.2.le⟩)
  simp only [norm_mul, norm_pow, Real.norm_of_nonneg (Real.exp_pos _).le, one_mul]
  calc
    ‖w‖ ^ n * ‖F w‖ ≤ ((n.factorial / c ^ n) * Real.exp (c * ‖w‖)) * M :=
      mul_le_mul hn (hM w ⟨hw.1.le, hw.2.le⟩) (norm_nonneg _) (by positivity)
    _ ≤ ((n.factorial / c ^ n) * (Real.exp (c * R) * Real.exp (c * |w.im|))) * M := by gcongr
    _ ≤ _ := by
      have ht := Real.add_one_le_exp (Real.exp (c * |w.im|))
      have ht' : Real.exp (c * |w.im|) ≤ Real.exp (Real.exp (c * |w.im|)) := by linarith
      calc
        _ = (M * (n.factorial / c ^ n) * Real.exp (c * R)) * Real.exp (c * |w.im|) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left ht' (by positivity)

/-- A polynomial growth bound on a closed strip extends to all heights by continuity. -/
theorem norm_le_rpow_on_closedStrip {f : ℂ → ℂ} {l u k : ℝ} (hk : 0 ≤ k)
    (hf : ContinuousOn f (Complex.re ⁻¹' Icc l u))
    (h : f =O[atHeight ⊓ 𝓟 (Complex.re ⁻¹' Icc l u)] fun z ↦ |z.im| ^ k) :
    ∃ C > (0 : ℝ), ∀ z : ℂ, z.re ∈ Icc l u → ‖f z‖ ≤ C * (1 + |z.im|) ^ k := by
  obtain ⟨C, hC, h⟩ := Asymptotics.isBigO_iff'.mp h
  rw [eventually_inf_principal, eventually_comap, eventually_atTop] at h
  obtain ⟨T, hT⟩ := h
  let K := Metric.closedBall (0 : ℂ) (|l| + |u| + T) ∩ Complex.re ⁻¹' Icc l u
  have hK : IsCompact K :=
    (isCompact_closedBall _ _).inter_right (isClosed_Icc.preimage Complex.continuous_re)
  obtain ⟨M, hM⟩ := hK.bddAbove_image (hf.norm.mono inter_subset_right)
  refine ⟨max C M, hC.trans_le (le_max_left ..), fun z hz ↦ ?_⟩
  have hbase : 1 ≤ 1 + |z.im| := le_add_of_nonneg_right (abs_nonneg _)
  by_cases ht : T ≤ |z.im|
  · have hb := hT _ ht z rfl hz
    rw [Real.norm_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)] at hb
    exact hb.trans (mul_le_mul (le_max_left ..)
      (Real.rpow_le_rpow (abs_nonneg _) (by linarith) hk)
      (Real.rpow_nonneg (abs_nonneg _) _) (hC.le.trans (le_max_left ..)))
  · have hzK : z ∈ K := by
      refine ⟨?_, hz⟩
      rw [Metric.mem_closedBall, dist_zero_right]
      have hre : |z.re| ≤ |l| + |u| :=
        abs_le.mpr ⟨by linarith [hz.1, neg_abs_le l, abs_nonneg u],
          by linarith [hz.2, le_abs_self u, abs_nonneg l]⟩
      exact (Complex.norm_le_abs_re_add_abs_im z).trans (by linarith)
    have hM' : ‖f z‖ ≤ M := hM (mem_image_of_mem (norm ∘ f) hzK)
    calc
      ‖f z‖ ≤ max C M := hM'.trans (le_max_right ..)
      _ ≤ _ := le_mul_of_one_le_right (hC.le.trans (le_max_left ..))
        (Real.one_le_rpow hbase hk)

/-- Nonnegative polynomial growth exponents on the two edges of a vertical strip
interpolate linearly at each interior real part under a uniform polynomial bound. -/
theorem isBigO_rpow_verticalStrip_interpolate {f : ℂ → ℂ} {l u K k₀ k₁ p q : ℝ}
    (hlu : l < u) (hK : 0 ≤ K) (hk₀ : 0 ≤ k₀) (hk₁ : 0 ≤ k₁)
    (hp : 0 ≤ p) (hq : 0 ≤ q) (hpq : p + q = 1)
    (hf : DifferentiableOn ℂ f (Complex.re ⁻¹' Icc l u))
    (h : f =O[atHeight ⊓ 𝓟 (Complex.re ⁻¹' Icc l u)] fun z ↦ |z.im| ^ K)
    (h₀ : f =O[atHeight ⊓ 𝓟 (Complex.re ⁻¹' {l})] fun z ↦ |z.im| ^ k₀)
    (h₁ : f =O[atHeight ⊓ 𝓟 (Complex.re ⁻¹' {u})] fun z ↦ |z.im| ^ k₁) :
    f =O[atHeight ⊓ 𝓟 (Complex.re ⁻¹' {p * l + q * u})]
      fun z ↦ |z.im| ^ (p * k₀ + q * k₁) := by
  obtain ⟨C, hC, hStrip⟩ := norm_le_rpow_on_closedStrip hK hf.continuousOn h
  obtain ⟨C₀, hC₀, hLeft⟩ := norm_le_rpow_on_closedStrip hk₀
    (hf.continuousOn.mono (preimage_mono (Icc_subset_Icc_right hlu.le))) (by simpa using h₀)
  obtain ⟨C₁, hC₁, hRight⟩ := norm_le_rpow_on_closedStrip hk₁
    (hf.continuousOn.mono (preimage_mono (Icc_subset_Icc_left hlu.le))) (by simpa using h₁)
  obtain ⟨n, hn⟩ := exists_nat_ge (max K (max k₀ k₁))
  have hnK : K ≤ (n : ℝ) := (le_max_left ..).trans hn
  have hn₀ : k₀ ≤ (n : ℝ) := (le_max_left ..).trans ((le_max_right ..).trans hn)
  have hn₁ : k₁ ≤ (n : ℝ) := (le_max_right ..).trans ((le_max_right ..).trans hn)
  let k := p * k₀ + q * k₁
  have hk : 0 ≤ k := by dsimp [k]; positivity
  have hHeight : Tendsto (fun z : ℂ ↦ |z.im|) atHeight atTop := tendsto_comap
  refine Asymptotics.IsBigO.of_bound
    ((1 + (u - l)) ^ n * ((C₀ * 2 ^ k₀) ^ p * (C₁ * 2 ^ k₁) ^ q) * 2 ^ k) ?_
  rw [eventually_inf_principal]
  filter_upwards [hHeight.eventually_ge_atTop 1] with z hzHeight hz
  have hzRe : z.re = p * l + q * u := hz
  have hzIcc : z.re ∈ Icc l u := by
    rw [hzRe]
    constructor
    · nlinarith [mul_nonneg hq (sub_nonneg.mpr hlu.le), congrArg (fun x : ℝ ↦ x * l) hpq]
    · nlinarith [mul_nonneg hp (sub_nonneg.mpr hlu.le), congrArg (fun x : ℝ ↦ x * u) hpq]
  let R := 1 + |z.im|
  let S := R + (u - l)
  let d := fun w : ℂ ↦ (S : ℂ) + (w - z)
  let F := fun w : ℂ ↦ f w * ((R : ℂ) / d w) ^ n
  have hR : 1 ≤ R := le_add_of_nonneg_right (abs_nonneg _)
  have hRpos : 0 < R := zero_lt_one.trans_le hR
  have hS : 0 < S := add_pos hRpos (sub_pos.mpr hlu)
  have hD (w : ℂ) (hw : w.re ∈ Icc l u) : R ≤ ‖d w‖ := by
    refine le_trans ?_ ((le_abs_self _).trans (Complex.abs_re_le_norm _))
    dsimp [d, S]
    linarith [hw.1, hzIcc.2]
  have hDpos (w : ℂ) (hw : w.re ∈ Icc l u) : 0 < ‖d w‖ := hRpos.trans_le (hD w hw)
  have hF : DifferentiableOn ℂ F (Complex.re ⁻¹' Icc l u) :=
    hf.mul (((differentiableOn_const (c := (R : ℂ))).div (by dsimp [d]; fun_prop)
      (fun w hw ↦ norm_pos_iff.mp (hDpos w hw))).pow n)
  have hBound (m A : ℝ) (hm : 0 ≤ m) (hmn : m ≤ n) (hA : 0 ≤ A)
      (w : ℂ) (hw : w.re ∈ Icc l u) (hwf : ‖f w‖ ≤ A * (1 + |w.im|) ^ m) :
      ‖F w‖ ≤ (A * 2 ^ m) * R ^ m := by
    let D := ‖d w‖
    have hD' : R ≤ D := hD w hw
    have hD₀ : 0 < D := hDpos w hw
    have hin : 1 + |w.im| ≤ 2 * D := by
      have him : |w.im - z.im| ≤ D := by
        simpa [D, d] using Complex.abs_im_le_norm (d w)
      have ht : |w.im| ≤ |w.im - z.im| + |z.im| := by
        simpa using abs_add_le (w.im - z.im) z.im
      dsimp [R] at hD'
      linarith
    have hratio : 1 ≤ D / R := (one_le_div hRpos).2 hD'
    have hpow : (D / R) ^ m ≤ (D / R) ^ n := by
      rw [← Real.rpow_natCast]
      exact Real.rpow_le_rpow_of_exponent_le hratio hmn
    have hcancel : D ^ m * (R / D) ^ n ≤ R ^ m := by
      rw [← inv_div, inv_pow, ← div_eq_mul_inv, div_le_iff₀ (by positivity)]
      rw [Real.div_rpow hD₀.le hRpos.le] at hpow
      exact (div_le_iff₀ (Real.rpow_pos_of_pos hRpos _)).mp hpow |>.trans_eq (mul_comm ..)
    simp only [F, norm_mul, norm_pow, norm_div, Complex.norm_real, Real.norm_of_nonneg hRpos.le]
    change ‖f w‖ * (R / D) ^ n ≤ _
    calc
      _ ≤ (A * (2 * D) ^ m) * (R / D) ^ n :=
        mul_le_mul_of_nonneg_right
          (hwf.trans (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity) hin hm) hA))
          (by positivity)
      _ = (A * 2 ^ m) * (D ^ m * (R / D) ^ n) := by
        rw [Real.mul_rpow (by norm_num) hD₀.le]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hcancel (by positivity)
  have hFstrip : DiffContOnCl ℂ F (Complex.re ⁻¹' Ioo l u) := by
    apply DifferentiableOn.diffContOnCl
    simpa only [Complex.HadamardThreeLines.verticalStrip, Complex.closure_preimage_re,
      closure_Ioo hlu.ne] using hF
  have hB : BddAbove ((norm ∘ F) '' Complex.HadamardThreeLines.verticalClosedStrip l u) := by
    refine ⟨(C * 2 ^ K) * R ^ K, ?_⟩
    rintro _ ⟨w, hw, rfl⟩
    exact hBound K C hK hnK hC.le w hw (hStrip w hw)
  have hL (w : ℂ) (hw : w ∈ Complex.re ⁻¹' {l}) : ‖F w‖ ≤ (C₀ * 2 ^ k₀) * R ^ k₀ := by
    have hw' : w.re = l := hw
    exact hBound k₀ C₀ hk₀ hn₀ hC₀.le w (by simpa [hw'] using hlu.le)
      (hLeft w (by simp [hw']))
  have hU (w : ℂ) (hw : w ∈ Complex.re ⁻¹' {u}) : ‖F w‖ ≤ (C₁ * 2 ^ k₁) * R ^ k₁ := by
    have hw' : w.re = u := hw
    exact hBound k₁ C₁ hk₁ hn₁ hC₁.le w (by simpa [hw'] using hlu.le)
      (hRight w (by simp [hw']))
  have hInterp := Complex.HadamardThreeLines.norm_le_interp_of_mem_verticalClosedStrip'
    hlu hzIcc hFstrip hB hL hU
  have hq' : (z.re - l) / (u - l) = q := by
    rw [div_eq_iff (sub_ne_zero.mpr hlu.ne.symm), hzRe]
    nlinarith [congrArg (fun x : ℝ ↦ x * l) hpq]
  rw [hq', show 1 - q = p by linarith,
    Real.mul_rpow (show 0 ≤ C₀ * 2 ^ k₀ by positivity) (show 0 ≤ R ^ k₀ by positivity),
    Real.mul_rpow (show 0 ≤ C₁ * 2 ^ k₁ by positivity) (show 0 ≤ R ^ k₁ by positivity),
    ← Real.rpow_mul hRpos.le, ← Real.rpow_mul hRpos.le] at hInterp
  have hInterp' : ‖F z‖ ≤ ((C₀ * 2 ^ k₀) ^ p * (C₁ * 2 ^ k₁) ^ q) * R ^ k := by
    convert hInterp using 1
    dsimp [k]
    rw [Real.rpow_add hRpos, mul_comm p k₀, mul_comm q k₁]
    ring
  have hSz : S ≤ (1 + (u - l)) * R := by
    dsimp [S]
    nlinarith [mul_nonneg (sub_nonneg.mpr hlu.le) (sub_nonneg.mpr hR)]
  have hfactor : (S / R) ^ n ≤ (1 + (u - l)) ^ n := by
    gcongr
    exact (div_le_iff₀ hRpos).2 hSz
  have hRk : R ^ k ≤ 2 ^ k * |z.im| ^ k := by
    rw [← Real.mul_rpow (by norm_num) (abs_nonneg _)]
    exact Real.rpow_le_rpow hRpos.le (by dsimp [R]; linarith) hk
  have hFz : ‖f z‖ = ‖F z‖ * (S / R) ^ n := by
    simp only [F, d, sub_self, add_zero, norm_mul, norm_pow, norm_div, Complex.norm_real,
      Real.norm_of_nonneg hRpos.le, Real.norm_of_nonneg hS.le, mul_assoc, ← mul_pow]
    rw [div_mul_div_cancel₀ hS.ne', div_self hRpos.ne', one_pow, mul_one]
  rw [Real.norm_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _), hFz]
  calc
    _ ≤ (((C₀ * 2 ^ k₀) ^ p * (C₁ * 2 ^ k₁) ^ q) * (2 ^ k * |z.im| ^ k)) *
        (1 + (u - l)) ^ n := by
      exact mul_le_mul (hInterp'.trans (mul_le_mul_of_nonneg_left hRk (by positivity)))
        hfactor (by positivity) (by positivity)
    _ = _ := by ring

/-- An exponential bound inside a vertical strip and polynomial bounds on both edges
give a uniform polynomial bound on the strip with the same boundary exponent. -/
theorem isBigO_pow_verticalStrip_of_exp {f : ℂ → ℂ} {a b B : ℝ} {n : ℕ}
    (hab : a < b) (hf : DifferentiableOn ℂ f (Complex.re ⁻¹' Icc a b))
    (hGrowth : f =O[atHeight ⊓ 𝓟 (Complex.re ⁻¹' Icc a b)]
      fun z ↦ Real.exp (B * |z.im|))
    (hLeft : f =O[atHeight ⊓ 𝓟 (Complex.re ⁻¹' {a})] fun z ↦ |z.im| ^ n)
    (hRight : f =O[atHeight ⊓ 𝓟 (Complex.re ⁻¹' {b})] fun z ↦ |z.im| ^ n) :
    f =O[atHeight ⊓ 𝓟 (Complex.re ⁻¹' Icc a b)] fun z ↦ |z.im| ^ n := by
  obtain ⟨A, hA, hLeft⟩ := norm_le_rpow_on_closedStrip (Nat.cast_nonneg n)
    (hf.continuousOn.mono (preimage_mono (Icc_subset_Icc_right hab.le)))
    (by simpa [Real.rpow_natCast] using hLeft)
  obtain ⟨D, hD, hRight⟩ := norm_le_rpow_on_closedStrip (Nat.cast_nonneg n)
    (hf.continuousOn.mono (preimage_mono (Icc_subset_Icc_left hab.le)))
    (by simpa [Real.rpow_natCast] using hRight)
  let g (z : ℂ) := f z / (z - ((a - 1 : ℝ) : ℂ)) ^ n
  have hBase (z : ℂ) (hz : a ≤ z.re) : 1 ≤ ‖z - ((a - 1 : ℝ) : ℂ)‖ := by
    refine le_trans ?_ (Complex.re_le_norm _)
    simp only [Complex.sub_re, Complex.ofReal_re]
    linarith
  have hg : DiffContOnCl ℂ g (Complex.re ⁻¹' Ioo a b) := by
    refine DifferentiableOn.diffContOnCl
      (DifferentiableOn.mono (t := Complex.re ⁻¹' Icc a b) ?_ ?_)
    · change DifferentiableOn ℂ (f / fun z ↦ (z - ((a - 1 : ℝ) : ℂ)) ^ n)
        (Complex.re ⁻¹' Icc a b)
      apply hf.div (by fun_prop)
      intro z hz
      exact pow_ne_zero _ (norm_pos_iff.mp (zero_lt_one.trans_le (hBase z hz.1)))
    · exact closure_minimal (preimage_mono Ioo_subset_Icc_self)
        (isClosed_Icc.preimage Complex.continuous_re)
  have hIm (z : ℂ) : |z.im| ≤ ‖z - ((a - 1 : ℝ) : ℂ)‖ := by
    simpa using Complex.abs_im_le_norm (z - ((a - 1 : ℝ) : ℂ))
  have hEdge (z : ℂ) {C : ℝ} (hC : 0 ≤ C) (hz : a ≤ z.re)
      (h : ‖f z‖ ≤ C * (1 + |z.im|) ^ (n : ℝ)) : ‖g z‖ ≤ C * 2 ^ n := by
    have hpos := zero_lt_one.trans_le (hBase z hz)
    simp only [g, norm_div, norm_pow, div_le_iff₀ (pow_pos hpos _)]
    rw [Real.rpow_natCast] at h
    calc
      ‖f z‖ ≤ C * (1 + |z.im|) ^ n := h
      _ ≤ C * (2 * ‖z - ((a - 1 : ℝ) : ℂ)‖) ^ n := by
        exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity)
          (by linarith [hBase z hz, hIm z]) n) hC
      _ = _ := by rw [mul_pow, mul_assoc]
  let c := Real.pi / (b - a) / 2
  have hc : 0 < c := by dsimp [c]; positivity
  let M := max B 0 / c
  have hExp : g =O[atHeight ⊓ 𝓟 (Complex.re ⁻¹' Ioo a b)]
      fun z ↦ Real.exp (M * Real.exp (c * |z.im|)) := by
    have hFilter : atHeight ⊓ 𝓟 (Complex.re ⁻¹' Ioo a b) ≤
        atHeight ⊓ 𝓟 (Complex.re ⁻¹' Icc a b) :=
      inf_le_inf_left _ (principal_mono.mpr (preimage_mono Ioo_subset_Icc_self))
    apply (Asymptotics.IsBigO.of_bound 1 ?_ :
      g =O[atHeight ⊓ 𝓟 (Complex.re ⁻¹' Ioo a b)] f).trans
        ((hGrowth.mono hFilter).trans ?_)
    · rw [eventually_inf_principal]
      exact Eventually.of_forall fun z (hz : z.re ∈ Ioo a b) ↦ by
        simp only [g, norm_div, norm_pow, one_mul]
        exact div_le_self (norm_nonneg _) (one_le_pow₀ (hBase z hz.1.le))
    · apply Asymptotics.IsBigO.of_bound 1 (Eventually.of_forall fun z ↦ ?_)
      simp only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), one_mul]
      apply Real.exp_le_exp.mpr
      calc
        B * |z.im| ≤ max B 0 * |z.im| :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (abs_nonneg _)
        _ = M * (c * |z.im|) := by simp [M, ← mul_assoc, hc.ne']
        _ ≤ M * Real.exp (c * |z.im|) := mul_le_mul_of_nonneg_left
          (by linarith [Real.add_one_le_exp (c * |z.im|)]) (by positivity)
  apply Asymptotics.IsBigO.of_bound ((max A D * 2 ^ n) * (|b - a + 1| + 1) ^ n)
  have hHeight : Tendsto (fun z : ℂ ↦ |z.im|)
      (atHeight ⊓ 𝓟 (Complex.re ⁻¹' Icc a b)) atTop := tendsto_inf_left tendsto_comap
  have hStrip : ∀ᶠ z in atHeight ⊓ 𝓟 (Complex.re ⁻¹' Icc a b), z.re ∈ Icc a b :=
    eventually_inf_principal.mpr (Eventually.of_forall fun _ hz ↦ hz)
  filter_upwards [hStrip, hHeight.eventually_ge_atTop (1 : ℝ)] with z hz ht
  have hBound := PhragmenLindelof.vertical_strip hg
    ⟨c, half_lt_self (div_pos Real.pi_pos (sub_pos.mpr hab)), M, hExp⟩
    (fun w hw ↦ (hEdge w hA.le hw.ge (hLeft w (by simp [hw]))).trans
      (mul_le_mul_of_nonneg_right (le_max_left A D) (by positivity)))
    (fun w hw ↦ (hEdge w hD.le (hw ▸ hab.le) (hRight w (by simp [hw]))).trans
      (mul_le_mul_of_nonneg_right (le_max_right A D) (by positivity))) hz.1 hz.2
  have hPos := pow_pos (zero_lt_one.trans_le (hBase z hz.1)) n
  simp only [g, norm_div, norm_pow, div_le_iff₀ hPos] at hBound
  have hSize : ‖z - ((a - 1 : ℝ) : ℂ)‖ ≤ (|b - a + 1| + 1) * |z.im| := by
    refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
    simp only [Complex.sub_re, Complex.ofReal_re, Complex.sub_im, Complex.ofReal_im, sub_zero]
    have hRe : |z.re - (a - 1)| ≤ |b - a + 1| := by
      rw [abs_of_nonneg (by linarith [hz.1] : 0 ≤ z.re - (a - 1))]
      linarith [hz.2, le_abs_self (b - a + 1)]
    nlinarith [hRe, mul_nonneg (abs_nonneg (b - a + 1)) (sub_nonneg.mpr ht)]
  rw [Real.norm_of_nonneg (pow_nonneg (abs_nonneg _) _)]
  calc
    ‖f z‖ ≤ (max A D * 2 ^ n) * ‖z - ((a - 1 : ℝ) : ℂ)‖ ^ n := hBound
    _ ≤ (max A D * 2 ^ n) * ((|b - a + 1| + 1) * |z.im|) ^ n :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hSize n)
        (mul_nonneg (hA.le.trans (le_max_left _ _)) (by positivity))
    _ = _ := by rw [mul_pow, mul_assoc (max A D * 2 ^ n)]

end InfoGeometry.Analysis.VerticalStripPhragmenLindelofHadamard

end noncomputable section
