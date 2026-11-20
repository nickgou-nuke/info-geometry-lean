/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Arithmetic.ActualRiemannZetaMobiusLSeriesBridge
import InfoGeometry.Arithmetic.RiemannHypothesisHalfPlaneReduction
import Mathlib.Analysis.MellinTransform
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Tactic.FieldSimp

/-!
# Mertens cancellation implies the native Riemann hypothesis

The existing owner supplies the actual reciprocal-zeta integral on `1 < re s`.
Here a bound on the actual Mertens function makes that integral holomorphic
on a larger half-plane. The native identity theorem extends
`riemannZeta₁ s * F s = s - 1` across that half-plane, including `s = 1`.
Away from that point the identity excludes zeta zeros. The existing functional
equation reduction then gives Mathlib's `RiemannHypothesis`.

This is a conditional implication from the existing
`MertensSquareRootCancellation` proposition. It does not prove cancellation or
the reverse implication. No unordered Möbius `LSeries` convergence in the
critical strip is asserted or used.
-/

noncomputable section

open scoped BigOperators Topology
open Asymptotics Filter MeasureTheory Set Complex

namespace InfoGeometry.Arithmetic.MertensMellinRiemannHypothesis

open MobiusMertensRHEquivalence ActualRiemannZetaMobiusLSeriesBridge

/-- The actual Mertens step function, cut off below the Mellin integration range. -/
def mertensCutoff (x : ℝ) : ℂ :=
  (Ioi (1 : ℝ)).indicator (fun t => (mertensFunction ⌊t⌋₊ : ℂ)) x

/-- A concrete candidate reciprocal, defined by the native Mellin transform. -/
def mertensMellin (s : ℂ) : ℂ := s * mellin mertensCutoff (-s)

/-- The step function is locally integrable; finite jumps do not obstruct integration. -/
theorem mertensCutoff_locallyIntegrableOn :
    LocallyIntegrableOn mertensCutoff (Ioi (0 : ℝ)) := by
  have hb : LocallyIntegrableOn (fun t : ℝ => (mertensFunction ⌊t⌋₊ : ℂ)) (Ici 0) := by
    simpa only [one_mul, mobius_partial_sum_eq_mertens_complex] using
      (locallyIntegrableOn_mul_sum_Icc (fun n : ℕ => (ArithmeticFunction.moebius n : ℂ))
        (m := 1) (a := 0) le_rfl (locallyIntegrableOn_const (1 : ℂ)))
  intro x hx
  obtain ⟨U, hU, hUint⟩ := hb.mono_set Ioi_subset_Ici_self x hx
  exact ⟨U, hU, hUint.indicator measurableSet_Ioi⟩

/-- An all-indices bound from the existing Mertens owner controls the real step function. -/
theorem mertensCutoff_isBigO_of_bound {r C : ℝ} (hr : 0 ≤ r) (hC : 0 ≤ C)
    (hM : ∀ N : ℕ, ‖(mertensFunction N : ℝ)‖ ≤ C * (N + 1 : ℝ) ^ r) :
    mertensCutoff =O[atTop] (fun x : ℝ => x ^ r) := by
  refine isBigO_iff.mpr ⟨C * 2 ^ r, ?_⟩
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
  have hx0 : 0 ≤ x := by linarith
  have hfloor : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le hx0
  have hb : ‖(mertensFunction ⌊x⌋₊ : ℂ)‖ ≤ C * (⌊x⌋₊ + 1 : ℝ) ^ r := by
    simpa using hM ⌊x⌋₊
  have hp : (⌊x⌋₊ + 1 : ℝ) ^ r ≤ (2 * x) ^ r :=
    Real.rpow_le_rpow (by positivity) (by linarith) hr
  simp only [mertensCutoff, indicator_of_mem (s := Ioi (1 : ℝ)) hx,
    Real.norm_of_nonneg (Real.rpow_nonneg hx0 r)]
  calc
    _ ≤ C * (⌊x⌋₊ + 1 : ℝ) ^ r := hb
    _ ≤ C * (2 * x) ^ r := mul_le_mul_of_nonneg_left hp hC
    _ = (C * 2 ^ r) * x ^ r := by rw [Real.mul_rpow (by norm_num) hx0]; ring

/-- The cutoff vanishes near zero, so it satisfies every power bound there. -/
theorem mertensCutoff_isBigO_zero (b : ℝ) :
    mertensCutoff =O[𝓝[>] (0 : ℝ)] (fun x : ℝ => x ^ (-b)) := by
  refine isBigO_iff.mpr ⟨0, ?_⟩
  filter_upwards [mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))]
    with x hx
  have hx1 : x < 1 := hx
  simp [mertensCutoff, not_lt.mpr hx1.le]

/-- Absolute integrability of the actual Mellin integral on the extended half-plane. -/
theorem mertensCutoff_mellinConvergent_of_bound {r C : ℝ}
    (hr : 0 ≤ r) (hC : 0 ≤ C)
    (hM : ∀ N : ℕ, ‖(mertensFunction N : ℝ)‖ ≤ C * (N + 1 : ℝ) ^ r)
    {s : ℂ} (hs : r < s.re) : MellinConvergent mertensCutoff (-s) := by
  apply mellinConvergent_of_isBigO_rpow (a := -r) (b := -s.re - 1)
    mertensCutoff_locallyIntegrableOn
  · simpa using mertensCutoff_isBigO_of_bound hr hC hM
  · simpa only [neg_re] using neg_lt_neg hs
  · exact mertensCutoff_isBigO_zero _
  · simp only [neg_re]; linarith

/-- Holomorphy is obtained from native Mellin differentiation and the supplied growth bound. -/
theorem mertensMellin_differentiableAt_of_bound {r C : ℝ}
    (hr : 0 ≤ r) (hC : 0 ≤ C)
    (hM : ∀ N : ℕ, ‖(mertensFunction N : ℝ)‖ ≤ C * (N + 1 : ℝ) ^ r)
    {s : ℂ} (hs : r < s.re) : DifferentiableAt ℂ mertensMellin s := by
  have hm : DifferentiableAt ℂ (mellin mertensCutoff) (-s) := by
    apply mellin_differentiableAt_of_isBigO_rpow (a := -r) (b := -s.re - 1)
      mertensCutoff_locallyIntegrableOn
    · simpa using mertensCutoff_isBigO_of_bound hr hC hM
    · simpa only [neg_re] using neg_lt_neg hs
    · exact mertensCutoff_isBigO_zero _
    · simp only [neg_re]; linarith
  exact differentiableAt_id.mul (hm.comp s differentiableAt_id.neg)

/-- The native Mellin convention `x^(z-1)` gives precisely the existing reciprocal integral. -/
theorem mertensMellin_eq_integral (s : ℂ) :
    mertensMellin s = s * ∫ t : ℝ in Ioi 1,
      (mertensFunction ⌊t⌋₊ : ℂ) * (t : ℂ) ^ (-(s + 1)) := by
  unfold mertensMellin mellin
  congr 1
  have hfun : (fun t : ℝ => (t : ℂ) ^ (-s - 1) • mertensCutoff t) =
      (Ioi (1 : ℝ)).indicator
        (fun t : ℝ => (mertensFunction ⌊t⌋₊ : ℂ) * (t : ℂ) ^ (-(s + 1))) := by
    funext t
    by_cases ht : t ∈ Ioi (1 : ℝ)
    · simp [mertensCutoff, ht, smul_eq_mul, show -(s + 1) = -s - 1 by ring, mul_comm]
    · simp [mertensCutoff, ht]
  rw [hfun, setIntegral_indicator measurableSet_Ioi,
    inter_eq_right.mpr (Ioi_subset_Ioi (by norm_num : (0 : ℝ) ≤ 1))]

/-- Reuse the established actual zeta/Möbius identity in its convergent region. -/
theorem mertensMellin_eq_zeta_inv {s : ℂ} (hs : 1 < s.re) :
    mertensMellin s = 1 / riemannZeta s := by
  rw [mertensMellin_eq_integral]
  exact (one_div_actualRiemannZeta_eq_mertens_integral_of_one_lt_re hs).symm

/-- The denominator-cleared reciprocal identity extends across the pole at one. -/
theorem regularizedZeta_mul_mertensMellin_of_bound {r C : ℝ}
    (hr : 0 ≤ r) (hr1 : r < 1) (hC : 0 ≤ C)
    (hM : ∀ N : ℕ, ‖(mertensFunction N : ℝ)‖ ≤ C * (N + 1 : ℝ) ^ r)
    {s : ℂ} (hs : r < s.re) :
    riemannZeta₁ s * mertensMellin s = s - 1 := by
  let U : Set ℂ := {z | r < z.re}
  have hUopen : IsOpen U := isOpen_lt continuous_const continuous_re
  have hUconn : IsPreconnected U :=
    ((convex_Ioi r).linear_preimage reLm).isPreconnected
  have hf : AnalyticOnNhd ℂ (fun z => riemannZeta₁ z * mertensMellin z) U := by
    apply DifferentiableOn.analyticOnNhd _ hUopen
    intro z hz
    exact ((differentiable_riemannZeta₁ z).mul
      (mertensMellin_differentiableAt_of_bound hr hC hM hz)).differentiableWithinAt
  have hg : AnalyticOnNhd ℂ (fun z : ℂ => z - 1) U :=
    fun z _ => analyticAt_id.sub analyticAt_const
  have heq : (fun z => riemannZeta₁ z * mertensMellin z) =ᶠ[𝓝 (2 : ℂ)]
      (fun z : ℂ => z - 1) := by
    filter_upwards [(isOpen_lt continuous_const continuous_re).mem_nhds
      (show 1 < (2 : ℂ).re by norm_num)] with z hz
    have hz1 : z ≠ 1 := by intro h; simp [h] at hz
    have hzz : riemannZeta z ≠ 0 := actualRiemannZeta_ne_zero_of_one_lt_re hz
    have hne : z - 1 ≠ 0 := sub_ne_zero.mpr hz1
    have hreg : riemannZeta₁ z = (z - 1) * riemannZeta z := by
      rw [riemannZeta_eq_inv_sub_mul hz1, ← mul_assoc, mul_inv_cancel₀ hne, one_mul]
    rw [mertensMellin_eq_zeta_inv hz, hreg]
    field_simp [hzz]
  have htwo : (2 : ℂ) ∈ U := by dsimp [U]; linarith only [hr1]
  exact (hf.eqOn_of_preconnected_of_eventuallyEq hg hUconn htwo heq) hs

/-- A Mertens power bound excludes actual zeta zeros strictly to its right. -/
theorem riemannZeta_ne_zero_of_mertens_bound {r C : ℝ}
    (hr : 0 ≤ r) (hr1 : r < 1) (hC : 0 ≤ C)
    (hM : ∀ N : ℕ, ‖(mertensFunction N : ℝ)‖ ≤ C * (N + 1 : ℝ) ^ r)
    {s : ℂ} (hs : r < s.re) (hs1 : s ≠ 1) : riemannZeta s ≠ 0 := by
  intro hz
  have hreg := riemannZeta_eq_inv_sub_mul hs1
  have hZ : riemannZeta₁ s = 0 := by
    rw [hz] at hreg
    exact (mul_eq_zero.mp hreg.symm).resolve_left (inv_ne_zero (sub_ne_zero.mpr hs1))
  have hid := regularizedZeta_mul_mertensMellin_of_bound hr hr1 hC hM hs
  rw [hZ, zero_mul] at hid
  exact hs1 (sub_eq_zero.mp hid.symm)

/-- A complete conditional route from the existing arithmetic cancellation
statement to Mathlib's precise Riemann hypothesis. -/
theorem riemannHypothesis_of_mertensSquareRootCancellation
    (hM : MertensSquareRootCancellation) : _root_.RiemannHypothesis := by
  apply RiemannHypothesisHalfPlaneReduction.riemannHypothesis_of_rightHalfPlane
  intro s hs hs1
  obtain ⟨r, hrhalf, hrtop⟩ := exists_between
    (lt_min hs (by norm_num : (1 : ℝ) / 2 < 1))
  obtain ⟨C, hC, hbound⟩ := mertens_growth_bound_of_square_root_cancellation hM hrhalf
  exact riemannZeta_ne_zero_of_mertens_bound (by linarith) (lt_of_lt_of_le hrtop (min_le_right _ _))
    hC hbound (lt_of_lt_of_le hrtop (min_le_left _ _)) hs1

end InfoGeometry.Arithmetic.MertensMellinRiemannHypothesis

end
