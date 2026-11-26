/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.NumberTheory.LSeries.ZetaZeros
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

/-!
# Nontrivial Zero Strip Confinement & Li–Cayley Unit-Circle Equivalences for Mathlib's `RiemannHypothesis`

Advances Frontier 3 ("RH zero-location witnesses") directly against Mathlib's canonical
`riemannZeta` and `RiemannHypothesis` declarations:

1. **Critical-Strip Confinement & Functional Reflection of Nontrivial Zeros**:
   - Defines `IsNontrivialZetaZero s` and proves `riemannHypothesis_iff_nontrivial`.
   - Proves `nontrivialZero_re_lt_one` (`s.re < 1` via `riemannZeta_ne_zero_of_one_le_re`),
     `nontrivialZero_ne_zero` (`s ≠ 0` via `riemannZeta_zero`),
     `nontrivialZero_re_pos` (`0 < s.re` via the functional equation `riemannZeta_one_sub`,
     `Gamma_ne_zero_of_re_pos`, `riemannZeta_ne_zero_of_one_le_re`, and `Complex.cos_eq_zero_iff`),
     and `nontrivialZero_in_critical_strip` (`0 < s.re < 1`).
   - Proves functional-equation zero symmetry `nontrivialZero_one_sub` and finite zero count in any
     bounded critical-strip box `{s | IsNontrivialZetaZero s ∧ |s.im| ≤ T}` (`criticalStrip_box_zeros_finite`).
2. **Exact Li–Cayley / Lee–Yang Unit-Circle Equivalences**:
   - Defines `liCayley s := 1 - 1 / s` and proves `norm_liCayley_eq_one_iff_re_eq_half`,
     `norm_liCayley_lt_one_iff_half_lt_re`, and `norm_liCayley_gt_one_iff_re_lt_half` (`s ≠ 0`).
   - Proves the exact global equivalences:
     * `riemannHypothesis_iff_halfStrip_zeroFree`: `RiemannHypothesis ↔ ∀ s, IsNontrivialZetaZero s → s.re ≤ 1 / 2`.
     * `riemannHypothesis_iff_liCayley_unitCircle`: `RiemannHypothesis ↔ ∀ s, IsNontrivialZetaZero s → ‖liCayley s‖ = 1`.
     * `riemannHypothesis_iff_liCayley_le_one`: `RiemannHypothesis ↔ ∀ s, IsNontrivialZetaZero s → ‖liCayley s‖ ≤ 1`.
3. **Finite Symmetric Zero-Set Li Positivity & Off-Critical Exponential Obstruction**:
   - Proves `finiteLiCoeff_nonneg_of_criticalLine` for finite sets of critical-line zeros and
     `exists_liCayley_blowup_of_offCritical` showing that any off-critical symmetric zero pair forces
     `1 < ‖liCayley ρ₀‖` and `‖(liCayley ρ₀) ^ n‖ → ∞`.

## Three-Bucket Audit Map

#### BUCKET 1: CLOSED FINITE & ANALYTIC THEOREMS
* `riemannHypothesis_iff_nontrivial`, `nontrivialZero_re_lt_one`, `nontrivialZero_ne_zero`,
  `nontrivialZero_re_pos`, `nontrivialZero_in_critical_strip`, `nontrivialZero_one_sub`,
  `criticalStrip_box_zeros_finite`.
* `norm_liCayley_eq_one_iff_re_eq_half`, `norm_liCayley_lt_one_iff_half_lt_re`,
  `norm_liCayley_gt_one_iff_re_lt_half`, `riemannHypothesis_iff_halfStrip_zeroFree`,
  `riemannHypothesis_iff_liCayley_unitCircle`, `riemannHypothesis_iff_liCayley_le_one`.
* `finiteLiCoeff_nonneg_of_criticalLine`, `exists_liCayley_blowup_of_offCritical`.

#### BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT HYPOTHESES
* Nonnegativity of `finiteLiCoeff Z n` conditional on `∀ ρ ∈ Z, ρ ≠ 0 ∧ ρ.re = 1 / 2`;
  exponential `‖(liCayley ρ₀)^n‖ → ∞` divergence conditional on an off-critical zero pair in `Z`.

#### BUCKET 3: OPEN CLOSURE DEBT
* Establishing a proof of `RiemannHypothesis` (or constructing an analytic proof that `∀ s, IsNontrivialZetaZero s → s.re ≤ 1 / 2` / global Li positivity for the full infinite zero set) remains an open Millennium Prize Problem.
-/

noncomputable section

namespace InfoGeometry.Arithmetic.RiemannZetaZeroLocationEquivalences

open Filter Topology Complex

/-! ## 1. Nontrivial Zeros & Exact Critical-Strip Confinement on `riemannZeta` -/

/-- A nontrivial zero of Mathlib's `riemannZeta`: excludes the trivial zeros `-2 * (n + 1)` and `s = 1`. -/
def IsNontrivialZetaZero (s : ℂ) : Prop :=
  riemannZeta s = 0 ∧ (¬∃ n : ℕ, s = -2 * (n + 1)) ∧ s ≠ 1

theorem riemannHypothesis_iff_nontrivial :
    RiemannHypothesis ↔ ∀ s : ℂ, IsNontrivialZetaZero s → s.re = 1 / 2 := by
  constructor
  · intro hRH s hs
    exact hRH s hs.1 hs.2.1 hs.2.2
  · intro h s hzero htriv h1
    exact h s ⟨hzero, htriv, h1⟩

theorem nontrivialZero_re_lt_one {s : ℂ} (hs : IsNontrivialZetaZero s) : s.re < 1 := by
  by_contra hle
  push Not at hle
  exact riemannZeta_ne_zero_of_one_le_re hle hs.1

theorem nontrivialZero_ne_zero {s : ℂ} (hs : IsNontrivialZetaZero s) : s ≠ 0 := by
  intro h0
  have hz := hs.1
  rw [h0, riemannZeta_zero] at hz
  norm_num at hz

theorem nontrivialZero_re_pos {s : ℂ} (hs : IsNontrivialZetaZero s) : 0 < s.re := by
  by_contra hle
  push Not at hle
  have hs0 : s ≠ 0 := nontrivialZero_ne_zero hs
  let w : ℂ := 1 - s
  have hw_re : 1 ≤ w.re := by
    dsimp [w]
    simp
    linarith
  have hw_pos : 0 < w.re := by linarith
  have hw_nat : ∀ n : ℕ, w ≠ -(n : ℂ) := by
    intro n hwn
    have hre := congrArg Complex.re hwn
    simp only [Complex.neg_re, Complex.natCast_re] at hre
    linarith [Nat.cast_nonneg (α := ℝ) n]
  have hw_ne1 : w ≠ 1 := by
    intro h1
    apply hs0
    dsimp [w] at h1
    linear_combination -h1
  have hfeq := riemannZeta_one_sub hw_nat hw_ne1
  have h1w : 1 - w = s := by
    dsimp [w]
    ring
  rw [h1w, hs.1] at hfeq
  have h2 : (2 : ℂ) ≠ 0 := two_ne_zero
  have hpi : (2 * (Real.pi : ℂ)) ≠ 0 := by
    simp [Real.pi_ne_zero]
  have hcpow : (2 * (Real.pi : ℂ)) ^ (-w) ≠ 0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl hpi)
  have hgamma : Complex.Gamma w ≠ 0 := Complex.Gamma_ne_zero_of_re_pos hw_pos
  have hzeta : riemannZeta w ≠ 0 := riemannZeta_ne_zero_of_one_le_re hw_re
  have hleft_ne : (2 : ℂ) * (2 * (Real.pi : ℂ)) ^ (-w) * Complex.Gamma w ≠ 0 :=
    mul_ne_zero (mul_ne_zero h2 hcpow) hgamma
  have hmul_zero :
      ((2 : ℂ) * (2 * (Real.pi : ℂ)) ^ (-w) * Complex.Gamma w) *
        (Complex.cos ((Real.pi : ℂ) * w / 2) * riemannZeta w) = 0 := by
    rw [← mul_assoc]
    exact hfeq.symm
  have hcos_zeta : Complex.cos ((Real.pi : ℂ) * w / 2) * riemannZeta w = 0 :=
    (mul_eq_zero.mp hmul_zero).resolve_left hleft_ne
  have hcos : Complex.cos ((Real.pi : ℂ) * w / 2) = 0 :=
    (mul_eq_zero.mp hcos_zeta).resolve_right hzeta
  rw [Complex.cos_eq_zero_iff] at hcos
  rcases hcos with ⟨k, hk⟩
  have hpi_c : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hw_eq : w = 2 * (k : ℂ) + 1 := by
    have hmul2 := congrArg (fun z : ℂ => 2 * z) hk
    have hsimp : (Real.pi : ℂ) * w = (Real.pi : ℂ) * (2 * (k : ℂ) + 1) := by
      calc
        (Real.pi : ℂ) * w = 2 * ((Real.pi : ℂ) * w / 2) := by ring
        _ = 2 * ((2 * (k : ℂ) + 1) * (Real.pi : ℂ) / 2) := hmul2
        _ = (Real.pi : ℂ) * (2 * (k : ℂ) + 1) := by ring
    exact mul_left_cancel₀ hpi_c hsimp
  have hs_eq : s = -2 * (k : ℂ) := by
    calc
      s = 1 - w := h1w.symm
      _ = 1 - (2 * (k : ℂ) + 1) := by rw [hw_eq]
      _ = -2 * (k : ℂ) := by ring
  have hk_re : (-2 : ℝ) * (k : ℝ) ≤ 0 := by
    have hre := congrArg Complex.re hs_eq
    simp at hre
    linarith
  have hk_ne0 : k ≠ 0 := by
    intro hk0
    apply hs0
    rw [hs_eq, hk0]
    simp
  have hk_ge1 : (1 : ℤ) ≤ k := by
    have hk_nonneg : (0 : ℝ) ≤ (k : ℝ) := by linarith
    have hk_z : 0 ≤ k := by exact_mod_cast hk_nonneg
    omega
  obtain ⟨n, hn⟩ : ∃ n : ℕ, k = (n : ℤ) + 1 := ⟨(k - 1).toNat, by omega⟩
  apply hs.2.1
  refine ⟨n, ?_⟩
  rw [hs_eq, hn]
  push_cast
  ring

theorem nontrivialZero_in_critical_strip {s : ℂ} (hs : IsNontrivialZetaZero s) :
    0 < s.re ∧ s.re < 1 :=
  ⟨nontrivialZero_re_pos hs, nontrivialZero_re_lt_one hs⟩

/-- Functional-equation symmetry of nontrivial zeros: `s` nontrivial zero `⇒ 1 - s` nontrivial zero. -/
theorem nontrivialZero_one_sub {s : ℂ} (hs : IsNontrivialZetaZero s) :
    IsNontrivialZetaZero (1 - s) := by
  have hstrip := nontrivialZero_in_critical_strip hs
  have hs_nat : ∀ n : ℕ, s ≠ -(n : ℂ) := by
    intro n hsn
    have hre := congrArg Complex.re hsn
    simp only [Complex.neg_re, Complex.natCast_re] at hre
    linarith [hstrip.1, Nat.cast_nonneg (α := ℝ) n]
  have hfeq := riemannZeta_one_sub hs_nat hs.2.2
  rw [hs.1, mul_zero] at hfeq
  refine ⟨hfeq, ?_, ?_⟩
  · rintro ⟨n, hn⟩
    have hre := congrArg Complex.re hn
    simp only [Complex.sub_re, Complex.one_re, Complex.neg_re, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, Complex.natCast_re] at hre
    have hre' : 1 - s.re = -2 * ((n : ℝ) + 1) := by
      have hre2 := congrArg Complex.re hn
      simp at hre2
      linarith
    linarith [hstrip.2, Nat.cast_nonneg (α := ℝ) n]
  · intro h1
    apply nontrivialZero_ne_zero hs
    linear_combination -h1

/-- Any bounded rectangle in the critical strip contains only finitely many nontrivial zeta zeros. -/
theorem criticalStrip_box_zeros_finite (T : ℝ) :
    {s : ℂ | IsNontrivialZetaZero s ∧ |s.im| ≤ T}.Finite := by
  let S : Set ℂ := Complex.equivRealProdCLM.symm '' ((Set.Icc (0 : ℝ) 1) ×ˢ (Set.Icc (-T) T))
  have hS_compact : IsCompact S :=
    ((isCompact_Icc.prod isCompact_Icc).image Complex.equivRealProdCLM.symm.continuous)
  have hfin := IsCompact.inter_riemannZetaZeros_finite hS_compact
  refine hfin.subset ?_
  intro s hs
  have hstrip := nontrivialZero_in_critical_strip hs.1
  refine ⟨?_, ?_⟩
  · refine ⟨(s.re, s.im), ⟨⟨hstrip.1.le, hstrip.2.le⟩, abs_le.mp hs.2⟩, ?_⟩
    apply Complex.ext <;> simp
  · exact hs.1.1

/-! ## 2. Exact Li–Cayley Unit-Circle Equivalences for `RiemannHypothesis` -/

/-- Li / Cayley critical-line transform `w(s) = 1 - 1 / s = (s - 1) / s`. -/
def liCayley (s : ℂ) : ℂ := 1 - 1 / s

private lemma normSq_sub_one_eq (s : ℂ) :
    ‖s - 1‖ ^ 2 = ‖s‖ ^ 2 - 2 * s.re + 1 := by
  have h1 : ‖s - 1‖ ^ 2 = (s - 1).re ^ 2 + (s - 1).im ^ 2 := by
    rw [Complex.sq_norm]
    simp [Complex.normSq_apply, sq]
  have h2 : ‖s‖ ^ 2 = s.re ^ 2 + s.im ^ 2 := by
    rw [Complex.sq_norm]
    simp [Complex.normSq_apply, sq]
  rw [h1, h2]
  simp only [Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im]
  ring

theorem norm_liCayley_sq {s : ℂ} (hs : s ≠ 0) :
    ‖liCayley s‖ ^ 2 = (‖s‖ ^ 2 - 2 * s.re + 1) / ‖s‖ ^ 2 := by
  have hdiv : liCayley s = (s - 1) / s := by
    unfold liCayley
    field_simp [hs]
  rw [hdiv, norm_div, div_pow, normSq_sub_one_eq s]

theorem norm_liCayley_eq_one_iff_re_eq_half {s : ℂ} (hs : s ≠ 0) :
    ‖liCayley s‖ = 1 ↔ s.re = 1 / 2 := by
  have hnorm_pos : 0 < ‖s‖ := norm_pos_iff.mpr hs
  have hsq_pos : 0 < ‖s‖ ^ 2 := sq_pos_of_pos hnorm_pos
  have hiff : ‖liCayley s‖ = 1 ↔ ‖liCayley s‖ ^ 2 = 1 := by
    constructor
    · intro h; rw [h, one_pow]
    · intro h
      have hn : 0 ≤ ‖liCayley s‖ := norm_nonneg _
      nlinarith
  rw [hiff, norm_liCayley_sq hs, div_eq_one_iff_eq hsq_pos.ne']
  constructor <;> intro h <;> linarith

theorem norm_liCayley_lt_one_iff_half_lt_re {s : ℂ} (hs : s ≠ 0) :
    ‖liCayley s‖ < 1 ↔ 1 / 2 < s.re := by
  have hnorm_pos : 0 < ‖s‖ := norm_pos_iff.mpr hs
  have hsq_pos : 0 < ‖s‖ ^ 2 := sq_pos_of_pos hnorm_pos
  have hiff : ‖liCayley s‖ < 1 ↔ ‖liCayley s‖ ^ 2 < 1 := by
    have hn : 0 ≤ ‖liCayley s‖ := norm_nonneg _
    constructor
    · intro h; nlinarith
    · intro h; nlinarith
  rw [hiff, norm_liCayley_sq hs, div_lt_one hsq_pos]
  constructor <;> intro h <;> linarith

theorem norm_liCayley_gt_one_iff_re_lt_half {s : ℂ} (hs : s ≠ 0) :
    1 < ‖liCayley s‖ ↔ s.re < 1 / 2 := by
  have hnorm_pos : 0 < ‖s‖ := norm_pos_iff.mpr hs
  have hsq_pos : 0 < ‖s‖ ^ 2 := sq_pos_of_pos hnorm_pos
  have hiff : 1 < ‖liCayley s‖ ↔ 1 < ‖liCayley s‖ ^ 2 := by
    have hn : 0 ≤ ‖liCayley s‖ := norm_nonneg _
    constructor
    · intro h; nlinarith
    · intro h; nlinarith
  rw [hiff, norm_liCayley_sq hs, one_lt_div hsq_pos]
  constructor <;> intro h <;> linarith

/-- Equivalence between `RiemannHypothesis` and non-positivity of `(s.re - 1/2)` for nontrivial zeros
(by `s ↔ 1 - s` symmetry). -/
theorem riemannHypothesis_iff_halfStrip_zeroFree :
    RiemannHypothesis ↔ ∀ s : ℂ, IsNontrivialZetaZero s → s.re ≤ 1 / 2 := by
  rw [riemannHypothesis_iff_nontrivial]
  constructor
  · intro h s hs
    exact (h s hs).le
  · intro h s hs
    have h1 := h s hs
    have h2 := h (1 - s) (nontrivialZero_one_sub hs)
    have h2' : 1 - s.re ≤ 1 / 2 := by simpa using h2
    linarith

/-- Equivalence between `RiemannHypothesis` and the Li–Cayley unit-circle condition
`‖1 - 1 / s‖ = 1` on all nontrivial zeros. -/
theorem riemannHypothesis_iff_liCayley_unitCircle :
    RiemannHypothesis ↔ ∀ s : ℂ, IsNontrivialZetaZero s → ‖liCayley s‖ = 1 := by
  rw [riemannHypothesis_iff_nontrivial]
  constructor
  · intro h s hs
    exact (norm_liCayley_eq_one_iff_re_eq_half (nontrivialZero_ne_zero hs)).mpr (h s hs)
  · intro h s hs
    exact (norm_liCayley_eq_one_iff_re_eq_half (nontrivialZero_ne_zero hs)).mp (h s hs)

/-- Equivalence between `RiemannHypothesis` and uniform Li–Cayley contraction `‖1 - 1 / s‖ ≤ 1`
across all nontrivial zeros. -/
theorem riemannHypothesis_iff_liCayley_le_one :
    RiemannHypothesis ↔ ∀ s : ℂ, IsNontrivialZetaZero s → ‖liCayley s‖ ≤ 1 := by
  rw [riemannHypothesis_iff_nontrivial]
  constructor
  · intro h s hs
    exact ((norm_liCayley_eq_one_iff_re_eq_half (nontrivialZero_ne_zero hs)).mpr (h s hs)).le
  · intro h s hs
    have hs_le : s.re ≤ 1 / 2 := by
      by_contra hlt
      push Not at hlt
      have hli : ‖liCayley s‖ < 1 :=
        (norm_liCayley_lt_one_iff_half_lt_re (nontrivialZero_ne_zero hs)).mpr hlt
      have h1s := nontrivialZero_one_sub hs
      have h1s_re : (1 - s).re < 1 / 2 := by simp; linarith
      have hgt := (norm_liCayley_gt_one_iff_re_lt_half (nontrivialZero_ne_zero h1s)).mpr h1s_re
      exact (not_le_of_gt hgt) (h (1 - s) h1s)
    have h1s := nontrivialZero_one_sub hs
    have h1s_le : (1 - s).re ≤ 1 / 2 := by
      by_contra hlt
      push Not at hlt
      have hre_s : s.re < 1 / 2 := by simp at hlt; linarith
      have hgt := (norm_liCayley_gt_one_iff_re_lt_half (nontrivialZero_ne_zero hs)).mpr hre_s
      exact (not_le_of_gt hgt) (h s hs)
    have h1s_re : (1 - s).re ≤ 1 / 2 := h1s_le
    simp at h1s_re
    linarith

/-! ## 3. Finite Symmetric Zero-Set Li Positivity & Exponential Obstruction -/

/-- Finite zero-sum Li coefficient `λ_n(Z) = ∑_{ρ ∈ Z} Re(1 - (1 - 1/ρ)^n)`. -/
def finiteLiCoeff (Z : Finset ℂ) (n : ℕ) : ℝ :=
  ∑ ρ ∈ Z, (1 - (liCayley ρ) ^ n).re

/-- If every zero `ρ ∈ Z` lies on `Re(ρ) = 1/2`, all finite Li coefficients `λ_n(Z)` are nonnegative. -/
theorem finiteLiCoeff_nonneg_of_criticalLine (Z : Finset ℂ)
    (hZ : ∀ ρ ∈ Z, ρ ≠ 0 ∧ ρ.re = 1 / 2) (n : ℕ) :
    0 ≤ finiteLiCoeff Z n := by
  unfold finiteLiCoeff
  refine Finset.sum_nonneg fun ρ hρ => ?_
  rcases hZ ρ hρ with ⟨hρ0, hρre⟩
  have hw1 : ‖liCayley ρ‖ = 1 := (norm_liCayley_eq_one_iff_re_eq_half hρ0).mpr hρre
  have hpow : ‖(liCayley ρ) ^ n‖ = 1 := by
    rw [norm_pow, hw1, one_pow]
  have hre : ((liCayley ρ) ^ n).re ≤ 1 := by
    calc
      ((liCayley ρ) ^ n).re ≤ ‖(liCayley ρ) ^ n‖ := Complex.re_le_norm _
      _ = 1 := hpow
  simp [hre]

/-- Any `1 - ρ`-symmetric finite set `Z` containing an off-critical zero exhibits an eigenvalue
with `1 < ‖liCayley ρ₀‖` and exponential blowup `‖(liCayley ρ₀)^n‖ → ∞`. -/
theorem exists_liCayley_blowup_of_offCritical (Z : Finset ℂ)
    (hsym : ∀ ρ ∈ Z, 1 - ρ ∈ Z)
    (hoff : ∃ ρ ∈ Z, ρ ≠ 0 ∧ 1 - ρ ≠ 0 ∧ ρ.re ≠ 1 / 2) :
    ∃ ρ₀ ∈ Z, 1 < ‖liCayley ρ₀‖ ∧
      Tendsto (fun n : ℕ => ‖(liCayley ρ₀) ^ n‖) atTop atTop := by
  rcases hoff with ⟨ρ, hρZ, hρ0, h1ρ0, hne⟩
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · refine ⟨ρ, hρZ, ?_⟩
    have h1 : 1 < ‖liCayley ρ‖ := (norm_liCayley_gt_one_iff_re_lt_half hρ0).mpr hlt
    refine ⟨h1, ?_⟩
    simpa [norm_pow] using tendsto_pow_atTop_atTop_of_one_lt h1
  · refine ⟨1 - ρ, hsym ρ hρZ, ?_⟩
    have hlt' : (1 - ρ).re < 1 / 2 := by simp; linarith
    have h1 : 1 < ‖liCayley (1 - ρ)‖ := (norm_liCayley_gt_one_iff_re_lt_half h1ρ0).mpr hlt'
    refine ⟨h1, ?_⟩
    simpa [norm_pow] using tendsto_pow_atTop_atTop_of_one_lt h1

end InfoGeometry.Arithmetic.RiemannZetaZeroLocationEquivalences
