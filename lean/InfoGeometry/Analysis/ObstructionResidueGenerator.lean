/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Analysis.RectangleVerticalCauchyIntegral
import Mathlib.Analysis.Normed.Algebra.GelfandFormula
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Tactic

/-!
# Obstruction residue generator

This owner proves the single-pole residue layer of the finite obstruction
generator. It does not claim the full Alpöge multi-pole amplification theorem:
the isolation of distinct poles inside one contour remains explicit debt.
-/

noncomputable section

open scoped BigOperators
open Set Filter Topology Polynomial spectrum
open InfoGeometry.Analysis.RectangleVerticalCauchyIntegral

namespace InfoGeometry.Analysis.ObstructionResidueGenerator

/-- Rectangle integral of a simple pole with positive natural multiplicity. -/
theorem rectangleIntegral_pole_nat (m : ℕ) (p z w : ℂ)
    (hp : p ∈ Ioo z.re w.re ×ℂ Ioo z.im w.im) :
    rectangleIntegral (fun s : ℂ => (m : ℂ) * (s - p)⁻¹) z w =
      2 * (Real.pi : ℂ) * Complex.I * (m : ℂ) := by
  rw [rectangleIntegral_const_mul, rectangleIntegral_sub_inv hp]
  ring

/-- The obstruction factor `-(m μ)/(1 - μ s)` is exactly the simple pole at
`s = μ⁻¹` with multiplicity `m`. -/
theorem obstructionFactor_eq_pole (m : ℕ) {μ : ℂ} (hμ : μ ≠ 0) :
    (fun s : ℂ => -((m : ℂ) * μ) / (1 - μ * s)) =
      fun s : ℂ => (m : ℂ) * (s - μ⁻¹)⁻¹ := by
  funext s
  have hden : 1 - μ * s = -μ * (s - μ⁻¹) := by
    field_simp [hμ]
    ring
  rw [hden]
  field_simp [hμ]

/-- Residue of a single obstruction factor at its pole `s = μ⁻¹`. -/
theorem obstructionFactor_residue (m : ℕ) {μ z w : ℂ} (hμ : μ ≠ 0)
    (hp : μ⁻¹ ∈ Ioo z.re w.re ×ℂ Ioo z.im w.im) :
    rectangleIntegral (fun s : ℂ => -((m : ℂ) * μ) / (1 - μ * s)) z w =
      2 * (Real.pi : ℂ) * Complex.I * (m : ℂ) := by
  rw [obstructionFactor_eq_pole m hμ]
  exact rectangleIntegral_pole_nat m μ⁻¹ z w hp

/-- Every obstruction pole carries a strictly positive natural multiplicity when
the family is nonempty and pointwise positive. -/
theorem obstruction_multiplicity_sum_pos {ι : Type*} (s : Finset ι)
    (m : ι → ℕ) (hs : s.Nonempty) (hm : ∀ j ∈ s, 0 < m j) :
    0 < ∑ j ∈ s, m j := by
  exact Finset.sum_pos (fun j hj => hm j hj) hs

/-- A factor is continuous on the rectangle boundary when its pole is strictly
inside the rectangle. -/
theorem obstructionFactor_continuousOn_boundary (m : ℕ) {μ z w : ℂ}
    (hμ : μ ≠ 0)
    (hp : μ⁻¹ ∈ Ioo z.re w.re ×ℂ Ioo z.im w.im) :
    ContinuousOn (fun s : ℂ => -((m : ℂ) * μ) / (1 - μ * s))
      ((Icc z.re w.re ×ℂ Icc z.im w.im) \ (Ioo z.re w.re ×ℂ Ioo z.im w.im)) := by
  apply ContinuousOn.div continuousOn_const
    (continuousOn_const.sub (continuousOn_const.mul continuousOn_id))
  intro s hs hzero
  change 1 - μ * s = 0 at hzero
  have hsmul : μ * s = 1 := by
    linear_combination -hzero
  have hs_eq : s = μ⁻¹ := by
    calc
      s = μ⁻¹ * (μ * s) := by field_simp [hμ]
      _ = μ⁻¹ := by rw [hsmul, mul_one]
  exact hs.2 (by simpa [hs_eq] using hp)

/-- Rectangle integral of a finite family of obstruction factors. Every pole
lies strictly inside the rectangle, so the residues add with positive natural
multiplicities. -/
theorem obstructionFactors_residue_sum {ι : Type*} (s : Finset ι)
    (m : ι → ℕ) (μ : ι → ℂ) {z w : ℂ}
    (hre : z.re ≤ w.re) (him : z.im ≤ w.im)
    (hμ : ∀ j ∈ s, μ j ≠ 0)
    (hp : ∀ j ∈ s, (μ j)⁻¹ ∈ Ioo z.re w.re ×ℂ Ioo z.im w.im) :
    rectangleIntegral (fun x : ℂ => ∑ j ∈ s, -((m j : ℂ) * μ j) / (1 - μ j * x)) z w =
      2 * (Real.pi : ℂ) * Complex.I * (∑ j ∈ s, (m j : ℂ)) := by
  rw [rectangleIntegral_finsetSum hre him]
  · calc
      (∑ j ∈ s, rectangleIntegral (fun x : ℂ => -((m j : ℂ) * μ j) / (1 - μ j * x)) z w)
          = ∑ j ∈ s, 2 * (Real.pi : ℂ) * Complex.I * (m j : ℂ) := by
              apply Finset.sum_congr rfl
              intro j hj
              exact obstructionFactor_residue (m j) (hμ j hj) (hp j hj)
      _ = 2 * (Real.pi : ℂ) * Complex.I * (∑ j ∈ s, (m j : ℂ)) := by
              rw [Finset.mul_sum]
  · intro j hj
    exact obstructionFactor_continuousOn_boundary (m j) (hμ j hj) (hp j hj)

/-- Finite obstruction trace on a specified index set. -/
def obstructionTraceOn {ι : Type*} (s : Finset ι) (m : ι → ℕ)
    (μ : ι → ℂ) (n : ℕ) : ℂ :=
  ∑ j ∈ s, (m j : ℂ) * (μ j) ^ n

/-- Finite geometric expansion of one obstruction factor up to order `N`. -/
theorem obstructionFactor_geometric (m : ℕ) (μ z : ℂ) (N : ℕ)
    (h : μ * z ≠ 1) :
    -∑ i ∈ Finset.range N, (m : ℂ) * μ ^ (i + 1) * z ^ i =
      -((m : ℂ) * μ) / (1 - μ * z) +
        ((m : ℂ) * μ * (μ * z) ^ N) / (1 - μ * z) := by
  have hden : 1 - μ * z ≠ 0 := by
    intro hz
    apply h
    linear_combination -hz
  field_simp [hden]
  have hsum :
      (∑ x ∈ Finset.range N, (m : ℂ) * μ ^ (x + 1) * z ^ x) =
        (m : ℂ) * μ * (∑ x ∈ Finset.range N, (μ * z) ^ x) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [pow_succ, mul_pow]
    ring
  rw [hsum, mul_assoc, geom_sum_mul_neg]
  ring

/-- The truncated obstruction generating polynomial equals the sum of the
simple-pole factors plus an explicit finite tail. -/
theorem obstructionGeneratingPolynomial_eq_factors {ι : Type*} (s : Finset ι)
    (m : ι → ℕ) (μ : ι → ℂ) (z : ℂ) (N : ℕ)
    (h : ∀ j ∈ s, μ j * z ≠ 1) :
    -∑ i ∈ Finset.range N, obstructionTraceOn s m μ (i + 1) * z ^ i =
      ∑ j ∈ s, (-((m j : ℂ) * μ j) / (1 - μ j * z) +
        ((m j : ℂ) * μ j * (μ j * z) ^ N) / (1 - μ j * z)) := by
  simp only [obstructionTraceOn]
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  exact obstructionFactor_geometric (m j) (μ j) z N (h j hj)

/-- `2πi` is nonzero, so a positive natural multiplicity gives a nonzero
residue. -/
theorem two_pi_I_ne_zero : 2 * (Real.pi : ℂ) * Complex.I ≠ 0 := by
  norm_num [Complex.ext_iff, Real.pi_ne_zero]

/-- A nonempty positive obstruction family has a nonzero total residue. -/
theorem residue_sum_ne_zero_of_nonempty {ι : Type*} (s : Finset ι)
    (m : ι → ℕ) (μ : ι → ℂ) {z w : ℂ}
    (hre : z.re ≤ w.re) (him : z.im ≤ w.im)
    (hs : s.Nonempty) (hm0 : ∀ j ∈ s, μ j ≠ 0)
    (hmpos : ∀ j ∈ s, 0 < m j)
    (hp : ∀ j ∈ s, (μ j)⁻¹ ∈ Ioo z.re w.re ×ℂ Ioo z.im w.im) :
    rectangleIntegral (fun x : ℂ => ∑ j ∈ s, -((m j : ℂ) * μ j) / (1 - μ j * x)) z w ≠ 0 := by
  rw [obstructionFactors_residue_sum s m μ hre him hm0 hp]
  apply mul_ne_zero
  · exact two_pi_I_ne_zero
  · exact_mod_cast (ne_of_gt (obstruction_multiplicity_sum_pos s m hs hmpos))

theorem obstructionTrace_spectralRadius_le_of_bound
    {s : ℕ} (μ : Fin s → ℂ) (m : Fin s → ℕ)
    (hinj : Function.Injective μ) (hm : ∀ j, 0 < m j)
    {C B : ℝ} (hB : 0 < B)
    (hbound : ∀ n : ℕ, 1 ≤ n →
      ‖obstructionTraceOn Finset.univ m μ n‖ ≤ C * B ^ n) :
    ∀ j, ‖μ j‖ ≤ B := by
  by_contra hnot
  push Not at hnot
  obtain ⟨j₁, hj₁⟩ := hnot
  have hne : (Finset.univ : Finset (Fin s)).Nonempty := ⟨j₁, Finset.mem_univ _⟩
  obtain ⟨j₀, -, hmax⟩ := Finset.exists_max_image Finset.univ (fun j => ‖μ j‖) hne
  let M : ℝ := ‖μ j₀‖
  have hBM : B < M := lt_of_lt_of_le hj₁ (hmax j₁ (Finset.mem_univ _))
  have hMpos : 0 < M := lt_trans hB hBM
  have hMne : (M : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hMpos)
  let lam : Fin s → ℂ := fun j => μ j / (M : ℂ)
  have hlam_inj : Function.Injective lam := by
    intro a b hab
    exact hinj (div_left_inj' hMne |>.mp hab)
  have hlam_j0_norm : ‖lam j₀‖ = 1 := by
    simp [lam, Complex.norm_real, M, div_self hMpos.ne']
  have hratio_lt : B / M < 1 := (div_lt_one hMpos).mpr hBM
  have hratio_nonneg : 0 ≤ B / M := div_nonneg hB.le hMpos.le
  have hS_tendsto : Tendsto (fun n : ℕ => ∑ j : Fin s, (m j : ℂ) * (lam j) ^ n) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero_norm' (a := fun n => C * (B / M) ^ n) ?_ ?_
    · filter_upwards [Filter.eventually_ge_atTop 1] with n hn
      rw [Real.norm_of_nonneg (norm_nonneg _)]
      have hpull :
          (∑ j : Fin s, (m j : ℂ) * (lam j) ^ n) =
            (obstructionTraceOn Finset.univ m μ n) / (M : ℂ) ^ n := by
        change (∑ j : Fin s, (m j : ℂ) * (lam j) ^ n) =
          (∑ j : Fin s, (m j : ℂ) * (μ j) ^ n) / (M : ℂ) ^ n
        rw [Finset.sum_div]
        refine Finset.sum_congr rfl fun j _ => ?_
        simp [lam, div_pow, mul_div_assoc]
      rw [hpull, norm_div, norm_pow, Complex.norm_real, Real.norm_of_nonneg hMpos.le,
        div_pow, ← mul_div_assoc]
      exact div_le_div_of_nonneg_right (hbound n hn) (pow_nonneg hMpos.le n)
    · have hpow : Tendsto (fun n : ℕ => (B / M) ^ n) atTop (𝓝 0) :=
        tendsto_pow_atTop_nhds_zero_of_lt_one hratio_nonneg hratio_lt
      simpa using hpow.const_mul C
  let P : ℂ[X] := ∏ i ∈ Finset.univ.erase j₀, (X - Polynomial.C (lam i))
  have hP_eval_j0 : P.eval (lam j₀) ≠ 0 := by
    rw [eval_prod]
    exact Finset.prod_ne_zero_iff.mpr fun i hi => by
      simp only [eval_sub, eval_X, eval_C, sub_ne_zero]
      exact fun h => (Finset.ne_of_mem_erase hi) (hlam_inj h.symm)
  have hP_eval_other : ∀ j : Fin s, j ≠ j₀ → P.eval (lam j) = 0 := by
    intro j hj
    rw [eval_prod]
    exact Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hj, Finset.mem_univ j⟩)
      (by simp)
  have hlin : ∀ n : ℕ,
      (m j₀ : ℂ) * P.eval (lam j₀) * (lam j₀) ^ n =
        ∑ r ∈ Finset.range (P.natDegree + 1),
          P.coeff r * (∑ j : Fin s, (m j : ℂ) * (lam j) ^ (n + r)) := by
    intro n
    have h1 :
        ∑ r ∈ Finset.range (P.natDegree + 1),
          P.coeff r * (∑ j : Fin s, (m j : ℂ) * (lam j) ^ (n + r)) =
        ∑ j : Fin s, (m j : ℂ) * P.eval (lam j) * (lam j) ^ n := by
      calc
        ∑ r ∈ Finset.range (P.natDegree + 1),
            P.coeff r * (∑ j : Fin s, (m j : ℂ) * (lam j) ^ (n + r))
            = ∑ r ∈ Finset.range (P.natDegree + 1),
                ∑ j : Fin s, P.coeff r * ((m j : ℂ) * (lam j) ^ (n + r)) := by
              refine Finset.sum_congr rfl fun r _ => Finset.mul_sum ..
        _ = ∑ j : Fin s, ∑ r ∈ Finset.range (P.natDegree + 1),
              P.coeff r * ((m j : ℂ) * (lam j) ^ (n + r)) := Finset.sum_comm
        _ = ∑ j : Fin s, (m j : ℂ) * P.eval (lam j) * (lam j) ^ n := by
              refine Finset.sum_congr rfl fun j _ => ?_
              rw [eval_eq_sum_range, Finset.mul_sum, Finset.sum_mul]
              refine Finset.sum_congr rfl fun r _ => ?_
              rw [pow_add]
              ring
    rw [h1, Finset.sum_eq_single j₀]
    · intro j _ hj
      rw [hP_eval_other j hj, mul_zero, zero_mul]
    · intro hmem
      exact (hmem (Finset.mem_univ j₀)).elim
  have hconst_tendsto :
      Tendsto (fun n : ℕ => ‖(m j₀ : ℂ) * P.eval (lam j₀) * (lam j₀) ^ n‖) atTop (𝓝 0) := by
    have hRHS :
        Tendsto (fun n : ℕ => ∑ r ∈ Finset.range (P.natDegree + 1),
          P.coeff r * (∑ j : Fin s, (m j : ℂ) * (lam j) ^ (n + r))) atTop (𝓝 0) := by
      have hterm : ∀ r ∈ Finset.range (P.natDegree + 1),
          Tendsto (fun n : ℕ => P.coeff r * (∑ j : Fin s, (m j : ℂ) * (lam j) ^ (n + r)))
            atTop (𝓝 0) := by
        intro r _
        have hshift :
            Tendsto (fun n : ℕ => ∑ j : Fin s, (m j : ℂ) * (lam j) ^ (n + r)) atTop (𝓝 0) :=
          hS_tendsto.comp (tendsto_add_atTop_nat r)
        simpa using hshift.const_mul (P.coeff r)
      simpa using tendsto_finsetSum (Finset.range (P.natDegree + 1)) hterm
    have hLHS : Tendsto (fun n : ℕ => (m j₀ : ℂ) * P.eval (lam j₀) * (lam j₀) ^ n) atTop (𝓝 0) :=
      hRHS.congr (fun n => (hlin n).symm)
    exact (tendsto_zero_iff_norm_tendsto_zero.mp hLHS)
  have hconst_eq : ∀ n : ℕ,
      ‖(m j₀ : ℂ) * P.eval (lam j₀) * (lam j₀) ^ n‖ = (m j₀ : ℝ) * ‖P.eval (lam j₀)‖ := by
    intro n
    rw [norm_mul, norm_mul, norm_pow, hlam_j0_norm, one_pow, mul_one, Complex.norm_natCast]
  have hzero : (m j₀ : ℝ) * ‖P.eval (lam j₀)‖ = 0 :=
    tendsto_nhds_unique (tendsto_const_nhds.congr (fun n => (hconst_eq n).symm)) hconst_tendsto
  have hpos : 0 < (m j₀ : ℝ) * ‖P.eval (lam j₀)‖ :=
    mul_pos (Nat.cast_pos.mpr (hm j₀)) (norm_pos_iff.mpr hP_eval_j0)
  exact (ne_of_gt hpos) hzero

theorem spectralRadius_le_of_norm_pow_bound
    {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A]
    (a : A) {B : ℝ} (hB : 0 ≤ B)
    (hbound : ∀ n : ℕ, 1 ≤ n → ‖a ^ n‖ ≤ B ^ n) :
    spectralRadius ℂ a ≤ ENNReal.ofReal B := by
  have hlim := pow_norm_pow_one_div_tendsto_nhds_spectralRadius a
  apply le_of_tendsto hlim
  filter_upwards [eventually_ge_atTop 1] with n hn
  apply ENNReal.ofReal_le_ofReal
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hpoweq : (B ^ n) ^ (1 / (n : ℝ)) = B := by
    rw [← Real.rpow_natCast B n, ← Real.rpow_mul hB]
    field_simp [hnpos.ne']
    simp
  calc
    ‖a ^ n‖ ^ (1 / (n : ℝ)) ≤ (B ^ n) ^ (1 / (n : ℝ)) := by
      exact Real.rpow_le_rpow (norm_nonneg _) (hbound n hn)
        (one_div_nonneg.mpr hnpos.le)
    _ = B := hpoweq

end InfoGeometry.Analysis.ObstructionResidueGenerator
