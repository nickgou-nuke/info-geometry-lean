/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.LSeries.SumCoeff
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Arithmetic.MobiusFiniteAbelSummation

/-!
# The actual Riemann-zeta/Möbius `LSeries` bridge

This owner exposes the analytic identity already available in Mathlib on the
half-plane `1 < re s`.  It deliberately does not assert analytic continuation,
an identity on the critical strip, or any Riemann-hypothesis consequence.
-/

noncomputable section

open scoped LSeries.notation

namespace InfoGeometry.Arithmetic.ActualRiemannZetaMobiusLSeriesBridge

open ArithmeticFunction
open Complex
open Asymptotics Filter MeasureTheory
open scoped BigOperators

private theorem mobius_norm_partial_sum_le (n : ℕ) :
    (∑ k ∈ Finset.Icc 1 n, ‖(moebius k : ℂ)‖) ≤ (n : ℝ) := by
  have hterm (k : ℕ) : ‖(moebius k : ℂ)‖ ≤ (1 : ℝ) := by
    norm_cast
    exact abs_moebius_le_one
  calc
    _ ≤ ∑ _k ∈ Finset.Icc 1 n, (1 : ℝ) :=
      Finset.sum_le_sum fun k _ => hterm k
    _ = (Finset.Icc 1 n).card := by simp
    _ = (n : ℝ) := by simp [Nat.card_Icc]

theorem mobius_LSeriesSummable_of_one_lt_re {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (↗(moebius : ArithmeticFunction ℂ)) s :=
  ArithmeticFunction.LSeriesSummable_moebius_iff.mpr hs

theorem not_mobius_LSeriesSummable_of_re_le_one {s : ℂ} (hs : s.re ≤ 1) :
    ¬ LSeriesSummable (↗(moebius : ArithmeticFunction ℂ)) s := by
  intro hsum
  exact (not_lt_of_ge hs) (ArithmeticFunction.LSeriesSummable_moebius_iff.mp hsum)

theorem mobius_LSeries_eq_partial_sum_integral_of_one_lt_re
    {s : ℂ} (hs : 1 < s.re) :
    L ↗(moebius : ArithmeticFunction ℂ) s =
      s * ∫ (t : ℝ) in Set.Ioi 1,
        (∑ k ∈ Finset.Icc 1 ⌊t⌋₊, (moebius k : ℂ)) *
          (t : ℂ) ^ (-(s + 1)) := by
  have hO' :
      (fun n : ℕ => ∑ k ∈ Finset.Icc 1 n, ‖(moebius k : ℂ)‖) =O[atTop]
        fun n : ℕ => (n : ℝ) := by
    refine (isBigO_nat_atTop_iff ?_).2 ⟨1, ?_⟩
    · intro n hn
      have hn0 : n = 0 := by exact_mod_cast hn
      subst n
      simp
    · intro n
      have hnonneg : 0 ≤ ∑ k ∈ Finset.Icc 1 n, ‖(moebius k : ℂ)‖ :=
        Finset.sum_nonneg fun _ _ => norm_nonneg _
      have hnreal : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
      simpa only [one_mul, Real.norm_of_nonneg hnonneg,
        Real.norm_of_nonneg hnreal] using mobius_norm_partial_sum_le n
  have hO :
      (fun n : ℕ => ∑ k ∈ Finset.Icc 1 n, ‖(moebius k : ℂ)‖) =O[atTop]
        fun n : ℕ => (n : ℝ) ^ (1 : ℝ) := by
    simpa [Real.rpow_one] using hO'
  change LSeries (fun n : ℕ => (moebius n : ℂ)) s = _
  exact LSeries_eq_mul_integral' _ (r := 1) (s := s) (by norm_num) (by exact hs) hO

private theorem mobius_partial_sum_eq_mertens_complex (N : ℕ) :
    (∑ k ∈ Finset.Icc 1 N, (moebius k : ℂ)) =
      (MobiusMertensRHEquivalence.mertensFunction N : ℂ) := by
  calc
    _ = ∑ k ∈ Finset.Icc 1 N, (moebius k : ℂ) * (1 : ℂ) := by simp
    _ = ∑ k ∈ Finset.range (N + 1), (moebius k : ℂ) * (1 : ℂ) :=
      (MobiusFiniteAbelSummation.mobius_sum_range_eq_Icc_complex
        (f := fun _ => (1 : ℂ)) N).symm
    _ = (MobiusMertensRHEquivalence.mertensFunction N : ℂ) := by
      simp [MobiusMertensRHEquivalence.mertensFunction]

theorem actualRiemannZeta_mul_mobius_LSeries_eq_one
    {s : ℂ} (hs : 1 < s.re) :
    riemannZeta s * L ↗(moebius : ArithmeticFunction ℂ) s = 1 := by
  rw [← ArithmeticFunction.LSeries_zeta_eq_riemannZeta hs]
  exact ArithmeticFunction.LSeries_zeta_mul_Lseries_moebius hs

theorem actualRiemannZeta_ne_zero_of_one_lt_re
    {s : ℂ} (hs : 1 < s.re) :
    riemannZeta s ≠ 0 := by
  rw [← ArithmeticFunction.LSeries_zeta_eq_riemannZeta hs]
  exact ArithmeticFunction.LSeries_zeta_ne_zero_of_one_lt_re hs

theorem mobius_LSeries_eq_actualRiemannZeta_inv
    {s : ℂ} (hs : 1 < s.re) :
    L ↗(moebius : ArithmeticFunction ℂ) s = (riemannZeta s)⁻¹ := by
  exact eq_inv_of_mul_eq_one_right
    (actualRiemannZeta_mul_mobius_LSeries_eq_one hs)

theorem one_div_actualRiemannZeta_eq_mobius_LSeries
    {s : ℂ} (hs : 1 < s.re) :
    1 / riemannZeta s = L ↗(moebius : ArithmeticFunction ℂ) s := by
  simpa [one_div] using
    (mobius_LSeries_eq_actualRiemannZeta_inv hs).symm

theorem one_div_actualRiemannZeta_eq_mertens_integral_of_one_lt_re
    {s : ℂ} (hs : 1 < s.re) :
    1 / riemannZeta s =
      s * ∫ (t : ℝ) in Set.Ioi 1,
        (MobiusMertensRHEquivalence.mertensFunction ⌊t⌋₊ : ℂ) *
          (t : ℂ) ^ (-(s + 1)) := by
  rw [one_div_actualRiemannZeta_eq_mobius_LSeries hs,
    mobius_LSeries_eq_partial_sum_integral_of_one_lt_re hs]
  congr 1
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  change (∑ k ∈ Finset.Icc 1 ⌊t⌋₊, (moebius k : ℂ)) *
    (t : ℂ) ^ (-(s + 1)) = _
  rw [mobius_partial_sum_eq_mertens_complex]

theorem eq_mobius_LSeries_of_mul_eq_one
    {s : ℂ} (hs : 1 < s.re) (F : ℂ)
    (hF : riemannZeta s * F = 1) :
    F = L ↗(moebius : ArithmeticFunction ℂ) s := by
  calc
    F = (riemannZeta s)⁻¹ := eq_inv_of_mul_eq_one_right hF
    _ = L ↗(moebius : ArithmeticFunction ℂ) s :=
      (mobius_LSeries_eq_actualRiemannZeta_inv hs).symm

end InfoGeometry.Arithmetic.ActualRiemannZetaMobiusLSeriesBridge
