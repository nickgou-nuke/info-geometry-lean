/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Möbius and Mertens conditional arithmetic estimates

This owner proves finite Mertens identities and ordered-series convergence from
explicit Mertens growth bounds. It defines the square-root-cancellation
proposition but does not prove it or establish an RH equivalence.
-/

noncomputable section

open Nat
open Finset
open ArithmeticFunction
open scoped ArithmeticFunction.Moebius Topology
open Asymptotics
open Filter

namespace InfoGeometry.Arithmetic.MobiusMertensRHEquivalence

/-- The Mertens function M(N) evaluates the summatory function of the Möbius function up to N. -/
def mertensFunction (N : ℕ) : ℤ :=
  ∑ n ∈ range (N + 1), μ n

theorem mertensFunction_zero :
    mertensFunction 0 = 0 := by
  norm_num [mertensFunction]

theorem mertensFunction_one :
    mertensFunction 1 = 1 := by
  rw [mertensFunction, show (1 + 1 : ℕ) = 2 by norm_num]
  rw [Finset.sum_range_succ]
  rw [Finset.sum_range_succ]
  simp

/- The finite summatory recurrence is the algebraic update rule for the
Mertens readout; no limiting or asymptotic statement is involved. -/
theorem mertensFunction_succ (N : ℕ) :
    mertensFunction (N + 1) = mertensFunction N + μ (N + 1) := by
  unfold mertensFunction
  rw [Finset.sum_range_succ]

private theorem mobius_shifted_prefix_eq_mertens (N : ℕ) :
    (∑ i ∈ Finset.range N, (moebius (i + 1) : ℝ)) =
      (mertensFunction N : ℝ) := by
  induction N with
  | zero => simp [mertensFunction_zero]
  | succ N ih =>
      rw [Finset.sum_range_succ, ih, ← Int.cast_add, ← mertensFunction_succ]

theorem mobius_ordered_series_tendsto_of_bounded_mertens
    {s B : ℝ} (hs : 0 < s)
    (hM : ∀ N, ‖(mertensFunction N : ℝ)‖ ≤ B) :
    ∃ l : ℝ, Tendsto
      (fun N : ℕ => ∑ n ∈ Finset.range N,
        ((n + 1 : ℝ) ^ (-s)) • (moebius (n + 1) : ℝ)) atTop (𝓝 l) := by
  let f : ℕ → ℝ := fun n => (n + 1 : ℝ) ^ (-s)
  let z : ℕ → ℝ := fun n => (moebius (n + 1) : ℝ)
  have hanti : Antitone f := by
    intro n m hnm
    exact
      (Real.antitoneOn_rpow_Ioi_of_exponent_nonpos (neg_nonpos.mpr hs.le))
        (Set.mem_Ioi.mpr (by positivity))
        (Set.mem_Ioi.mpr (by positivity))
        (by exact_mod_cast Nat.add_le_add_right hnm 1)
  have hbase : Tendsto (fun n : ℕ => (n + 1 : ℝ)) atTop atTop :=
    tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
  have hzero : Tendsto f atTop (𝓝 0) := by
    exact (tendsto_rpow_neg_atTop hs).comp hbase
  have hbound : ∀ N, ‖∑ i ∈ Finset.range N, z i‖ ≤ B := by
    intro N
    rw [show (∑ i ∈ Finset.range N, z i) = (mertensFunction N : ℝ) by
      simp only [z]
      exact mobius_shifted_prefix_eq_mertens N]
    exact hM N
  have hcauchy : CauchySeq (fun N : ℕ => ∑ n ∈ Finset.range N, f n • z n) :=
    Antitone.cauchySeq_series_mul_of_tendsto_zero_of_bounded hanti hzero hbound
  have hlim := cauchySeq_tendsto_of_complete hcauchy
  refine ⟨hlim.choose, ?_⟩
  simpa only [f, z, smul_eq_mul, mul_comm] using hlim.choose_spec

theorem mobius_ordered_series_tendsto_of_bounded_weighted_prefix
    {a s B : ℝ} (has : a < s)
    (hA : ∀ N, ‖∑ n ∈ Finset.range N,
      ((n + 1 : ℝ) ^ (-a)) • (moebius (n + 1) : ℝ)‖ ≤ B) :
    ∃ l : ℝ, Tendsto
      (fun N : ℕ => ∑ n ∈ Finset.range N,
        ((n + 1 : ℝ) ^ (-(s - a))) •
          (((n + 1 : ℝ) ^ (-a)) • (moebius (n + 1) : ℝ))) atTop (𝓝 l) := by
  let f : ℕ → ℝ := fun n => (n + 1 : ℝ) ^ (-(s - a))
  let z : ℕ → ℝ := fun n => (n + 1 : ℝ) ^ (-a) • (moebius (n + 1) : ℝ)
  have hanti : Antitone f := by
    intro n m hnm
    exact
      (Real.antitoneOn_rpow_Ioi_of_exponent_nonpos
        (neg_nonpos.mpr (sub_nonneg.mpr has.le)))
        (Set.mem_Ioi.mpr (by positivity))
        (Set.mem_Ioi.mpr (by positivity))
        (by exact_mod_cast Nat.add_le_add_right hnm 1)
  have hbase : Tendsto (fun n : ℕ => (n + 1 : ℝ)) atTop atTop :=
    tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
  have hzero : Tendsto f atTop (𝓝 0) := by
    exact (tendsto_rpow_neg_atTop (sub_pos.mpr has)).comp hbase
  have hbound : ∀ N, ‖∑ n ∈ Finset.range N, z n‖ ≤ B := by
    intro N
    simpa [z] using hA N
  have hcauchy : CauchySeq (fun N : ℕ => ∑ n ∈ Finset.range N, f n • z n) :=
    Antitone.cauchySeq_series_mul_of_tendsto_zero_of_bounded hanti hzero hbound
  have hlim := cauchySeq_tendsto_of_complete hcauchy
  refine ⟨hlim.choose, ?_⟩
  simpa only [f, z] using hlim.choose_spec

private theorem rpow_decrement_le {a : ℝ} (ha : 0 < a) (n : ℕ) :
    (n + 1 : ℝ) ^ (-a) - (n + 2 : ℝ) ^ (-a) ≤
      a * (n + 1 : ℝ) ^ (-a - 1) := by
  let x : ℝ := n + 1
  have hx : 0 < x := by positivity
  have hxab : x < x + 1 := by linarith
  have hcont : ContinuousOn (fun y : ℝ => y ^ (-a)) (Set.Icc x (x + 1)) := by
    apply continuousOn_id.rpow_const
    intro y hy
    exact Or.inl (ne_of_gt (lt_of_lt_of_le hx hy.1))
  have hderiv : ∀ y ∈ Set.Ioo x (x + 1),
      HasDerivAt (fun y : ℝ => y ^ (-a)) ((-a) * y ^ (-a - 1)) y := by
    intro y hy
    simpa [sub_eq_add_neg] using
      (Real.hasDerivAt_rpow_const (x := y) (p := -a)
        (Or.inl (ne_of_gt (lt_trans hx hy.1))))
  obtain ⟨c, hc, hcderiv⟩ :=
    exists_hasDerivAt_eq_slope (f := fun y : ℝ => y ^ (-a))
      (f' := fun y : ℝ => (-a) * y ^ (-a - 1)) hxab hcont hderiv
  have hdiff : x ^ (-a) - (x + 1) ^ (-a) = a * c ^ (-a - 1) := by
    have hc' : (-a) * c ^ (-a - 1) = (x + 1) ^ (-a) - x ^ (-a) := by
      simpa using hcderiv
    calc
      x ^ (-a) - (x + 1) ^ (-a) = -((x + 1) ^ (-a) - x ^ (-a)) := by ring
      _ = -((-a) * c ^ (-a - 1)) := by rw [hc']
      _ = a * c ^ (-a - 1) := by ring
  have hpow : c ^ (-a - 1) ≤ x ^ (-a - 1) := by
    apply (Real.antitoneOn_rpow_Ioi_of_exponent_nonpos (by linarith : -a - 1 ≤ 0))
    · exact Set.mem_Ioi.mpr hx
    · exact Set.mem_Ioi.mpr (lt_trans hx hc.1)
    · exact le_of_lt hc.1
  have hcast : (n + 2 : ℝ) = x + 1 := by
    dsimp [x]
    ring
  rw [show (n + 1 : ℝ) = x by rfl, hcast]
  calc
    x ^ (-a) - (x + 1) ^ (-a) = a * c ^ (-a - 1) := hdiff
    _ ≤ a * x ^ (-a - 1) := mul_le_mul_of_nonneg_left hpow ha.le

private theorem shifted_mobius_weight_eq_cutoff_sum (a : ℝ) (N : ℕ) :
    (∑ i ∈ Finset.range N, (moebius (i + 1) : ℝ) * (i + 1 : ℝ) ^ (-a)) =
      ∑ n ∈ Finset.range (N + 1), (moebius n : ℝ) *
        (if n = 0 then 0 else (n : ℝ) ^ (-a)) := by
  rw [Finset.sum_range_succ']
  simp

private def realPrefix (a : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (n + 1), a k

private theorem finite_summation_by_parts_real (a f : ℕ → ℝ) (N : ℕ) :
    (∑ n ∈ Finset.range (N + 1), a n * f n) =
      realPrefix a N * f N +
        ∑ n ∈ Finset.range N, realPrefix a n * (f n - f (n + 1)) := by
  induction N with
  | zero => simp [realPrefix]
  | succ N ih =>
      rw [Finset.sum_range_succ, ih]
      have hp : realPrefix a (N + 1) = realPrefix a N + a (N + 1) := by
        unfold realPrefix
        rw [Finset.sum_range_succ]
      rw [hp, Finset.sum_range_succ]
      ring

private theorem mobius_weighted_prefix_abel_formula (a : ℝ) (N : ℕ) :
    (∑ i ∈ Finset.range N, (moebius (i + 1) : ℝ) * (i + 1 : ℝ) ^ (-a)) =
      (mertensFunction N : ℝ) * (if N = 0 then 0 else (N : ℝ) ^ (-a)) +
        ∑ n ∈ Finset.range N, (mertensFunction n : ℝ) *
          ((if n = 0 then 0 else (n : ℝ) ^ (-a)) -
            (if n + 1 = 0 then 0 else (n + 1 : ℝ) ^ (-a))) := by
  rw [shifted_mobius_weight_eq_cutoff_sum]
  have h := finite_summation_by_parts_real
    (fun n => (moebius n : ℝ))
    (fun n => if n = 0 then 0 else (n : ℝ) ^ (-a)) N
  simpa [realPrefix, mertensFunction] using h

private theorem succ_rpow_le_two_mul_rpow {r : ℝ} (hr : 0 ≤ r)
    {n : ℕ} (hn : 1 ≤ n) :
    (n + 1 : ℝ) ^ r ≤ (2 : ℝ) ^ r * (n : ℝ) ^ r := by
  have hnreal : 1 ≤ (n : ℝ) := by exact_mod_cast hn
  have hle : (n + 1 : ℝ) ≤ 2 * (n : ℝ) := by linarith
  calc
    (n + 1 : ℝ) ^ r ≤ (2 * (n : ℝ)) ^ r :=
      Real.rpow_le_rpow (by positivity) hle hr
    _ = (2 : ℝ) ^ r * (n : ℝ) ^ r :=
      Real.mul_rpow (by norm_num) (by positivity)

private theorem boundary_power_bound {r a : ℝ} (hr : 0 ≤ r) (hra : r < a)
    {n : ℕ} (hn : 1 ≤ n) :
    (n + 1 : ℝ) ^ r * (n : ℝ) ^ (-a) ≤ (2 : ℝ) ^ r := by
  have hscale := succ_rpow_le_two_mul_rpow hr hn
  have hneg : (n : ℝ) ^ (r - a) ≤ 1 := by
    have h := @Real.rpow_le_rpow_of_nonpos (1 : ℝ) (n : ℝ) (r - a)
      (by norm_num) (by exact_mod_cast hn) (sub_nonpos.mpr hra.le)
    simpa using h
  calc
    (n + 1 : ℝ) ^ r * (n : ℝ) ^ (-a) ≤
        ((2 : ℝ) ^ r * (n : ℝ) ^ r) * (n : ℝ) ^ (-a) :=
      mul_le_mul_of_nonneg_right hscale (Real.rpow_nonneg (Nat.cast_nonneg n) _)
    _ = (2 : ℝ) ^ r * ((n : ℝ) ^ r * (n : ℝ) ^ (-a)) := by ring
    _ = (2 : ℝ) ^ r * (n : ℝ) ^ (r - a) := by
      rw [← Real.rpow_add (by positivity : 0 < (n : ℝ)) r (-a)]
      simpa [sub_eq_add_neg]
    _ ≤ (2 : ℝ) ^ r := by
      simpa using mul_le_mul_of_nonneg_left hneg
        (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) r)

private theorem remainder_term_bound
    {r a C : ℝ} (hr : 0 ≤ r) (hra : r < a) (ha : 0 < a) (hC : 0 ≤ C)
    (n : ℕ)
    (hM : ‖(mertensFunction n : ℝ)‖ ≤ C * (n + 1 : ℝ) ^ r) :
    ‖(mertensFunction n : ℝ) *
        ((if n = 0 then 0 else (n : ℝ) ^ (-a)) -
          (if n + 1 = 0 then 0 else (n + 1 : ℝ) ^ (-a)))‖ ≤
      C * a * (2 : ℝ) ^ r * (n : ℝ) ^ (r - a - 1) := by
  by_cases hn0 : n = 0
  · subst n
    have hp : r - a - 1 < 0 := by linarith [hra]
    have hz : (0 : ℝ) ^ (r - a - 1) = 0 := Real.zero_rpow (ne_of_lt hp)
    simp [mertensFunction_zero, hz]
  · have hnpos : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn0
    have hnreal : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn0
    have hscale := succ_rpow_le_two_mul_rpow hr hnpos
    have hdropNonneg : 0 ≤ (n : ℝ) ^ (-a) - (n + 1 : ℝ) ^ (-a) := by
      apply sub_nonneg.mpr
      exact Real.rpow_le_rpow_of_nonpos hnreal
        (by exact_mod_cast Nat.le_succ n) (neg_nonpos.mpr ha.le)
    have hdrop : (n : ℝ) ^ (-a) - (n + 1 : ℝ) ^ (-a) ≤
        a * (n : ℝ) ^ (-a - 1) := by
      obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn0
      convert rpow_decrement_le ha m using 1 <;> simp only [Nat.cast_succ] <;> ring_nf
    simp [hn0, Real.norm_of_nonneg hdropNonneg]
    calc
      _ ≤ (C * (n + 1 : ℝ) ^ r) * (a * (n : ℝ) ^ (-a - 1)) :=
        mul_le_mul hM hdrop (by positivity) (by positivity)
      _ ≤ C * a * (2 : ℝ) ^ r * (n : ℝ) ^ (r - a - 1) := by
        calc
          _ = (C * a * (n : ℝ) ^ (-a - 1)) * (n + 1 : ℝ) ^ r := by ring
          _ ≤ (C * a * (n : ℝ) ^ (-a - 1)) *
                ((2 : ℝ) ^ r * (n : ℝ) ^ r) := by
            exact mul_le_mul_of_nonneg_left hscale
              (mul_nonneg (mul_nonneg hC ha.le) (Real.rpow_nonneg hnreal.le _))
          _ = C * a * (2 : ℝ) ^ r *
                ((n : ℝ) ^ (-a - 1) * (n : ℝ) ^ r) := by ring
          _ = C * a * (2 : ℝ) ^ r * (n : ℝ) ^ (r - a - 1) := by
            rw [← Real.rpow_add hnreal (-a - 1) r]
            congr 1
            ring

/-- A polynomial Mertens bound with exponent `r < a` gives a uniform bound on the
weighted Möbius prefixes; the derivative estimate supplies the crucial extra `1/n`
in the summation-by-parts remainder. -/
theorem mobius_weighted_prefix_bounded_of_mertens_growth
    {r a C : ℝ} (hr : 0 ≤ r) (hra : r < a) (ha : 0 < a) (hC : 0 ≤ C)
    (hM : ∀ N, ‖(mertensFunction N : ℝ)‖ ≤ C * (N + 1 : ℝ) ^ r) :
    ∃ B, ∀ N, ‖∑ n ∈ Finset.range N,
      ((n + 1 : ℝ) ^ (-a)) • (moebius (n + 1) : ℝ)‖ ≤ B := by
  let p : ℝ := r - a - 1
  let q : ℕ → ℝ := fun n => (n : ℝ) ^ p
  have hp : p < -1 := by dsimp [p]; linarith
  have hq : Summable q := by
    dsimp [q, p]
    exact Real.summable_nat_rpow.mpr hp
  let T : ℝ := ∑' n, q n
  let K : ℝ := C * a * (2 : ℝ) ^ r
  let B : ℝ := C * (2 : ℝ) ^ r + K * T
  have hqnonneg : ∀ n, 0 ≤ q n := fun n => Real.rpow_nonneg (Nat.cast_nonneg n) _
  have hTnonneg : 0 ≤ T := by
    dsimp [T]
    exact tsum_nonneg hqnonneg
  have hKnonneg : 0 ≤ K := by
    dsimp [K]
    positivity
  have hcoeffnonneg : 0 ≤ C * (2 : ℝ) ^ r := by positivity
  let f : ℕ → ℝ := fun n => if n = 0 then 0 else (n : ℝ) ^ (-a)
  have hBoundary (N : ℕ) :
      ‖(mertensFunction N : ℝ) * f N‖ ≤ C * (2 : ℝ) ^ r := by
    by_cases hN : N = 0
    · subst N
      simpa [f, mertensFunction_zero] using hcoeffnonneg
    · have hNpos : 1 ≤ N := Nat.one_le_iff_ne_zero.mpr hN
      have hweight : 0 ≤ (N : ℝ) ^ (-a) := Real.rpow_nonneg (Nat.cast_nonneg _) _
      simp [f, hN, Real.norm_of_nonneg hweight]
      calc
        ‖(mertensFunction N : ℝ)‖ * (N : ℝ) ^ (-a) ≤
            C * (N + 1 : ℝ) ^ r * (N : ℝ) ^ (-a) :=
          mul_le_mul_of_nonneg_right (hM N) hweight
        _ ≤ C * ((N + 1 : ℝ) ^ r * (N : ℝ) ^ (-a)) := by rw [mul_assoc]
        _ ≤ C * (2 : ℝ) ^ r :=
          mul_le_mul_of_nonneg_left (boundary_power_bound hr hra hNpos) hC
  have hRemainder (N : ℕ) :
      ‖∑ n ∈ Finset.range N,
          (mertensFunction n : ℝ) * (f n - f (n + 1))‖ ≤ K * T := by
    calc
      _ ≤ ∑ n ∈ Finset.range N,
          ‖(mertensFunction n : ℝ) * (f n - f (n + 1))‖ := norm_sum_le _ _
      _ ≤ ∑ n ∈ Finset.range N, K * q n :=
        Finset.sum_le_sum fun n hn => by
          simpa [K, q, p, f] using remainder_term_bound hr hra ha hC n (hM n)
      _ = K * ∑ n ∈ Finset.range N, q n := by rw [Finset.mul_sum]
      _ ≤ K * T := by
        apply mul_le_mul_of_nonneg_left
          (hq.sum_le_tsum (Finset.range N) fun n hn => hqnonneg n)
          hKnonneg
  have hformula (N : ℕ) :
      (∑ n ∈ Finset.range N, (moebius (n + 1) : ℝ) * (n + 1 : ℝ) ^ (-a)) =
        (mertensFunction N : ℝ) * f N +
          ∑ n ∈ Finset.range N, (mertensFunction n : ℝ) * (f n - f (n + 1)) := by
    simpa [f] using mobius_weighted_prefix_abel_formula a N
  refine ⟨B, fun N => ?_⟩
  have hmulBound :
      ‖∑ n ∈ Finset.range N, (moebius (n + 1) : ℝ) * (n + 1 : ℝ) ^ (-a)‖ ≤ B := by
    rw [hformula]
    calc
      ‖(mertensFunction N : ℝ) * f N +
          ∑ n ∈ Finset.range N, (mertensFunction n : ℝ) * (f n - f (n + 1))‖ ≤
          ‖(mertensFunction N : ℝ) * f N‖ +
            ‖∑ n ∈ Finset.range N, (mertensFunction n : ℝ) * (f n - f (n + 1))‖ :=
        norm_add_le _ _
      _ ≤ C * (2 : ℝ) ^ r + K * T := add_le_add (hBoundary N) (hRemainder N)
      _ = B := by rfl
  simpa only [smul_eq_mul, mul_comm] using hmulBound

/-- A polynomial Mertens bound with exponent below `a` implies convergence of the
ordered Möbius series at every real exponent `s` with `a < s`. -/
theorem mobius_ordered_series_tendsto_of_mertens_growth
    {r a s C : ℝ} (hr : 0 ≤ r) (hra : r < a) (has : a < s) (hC : 0 ≤ C)
    (hM : ∀ N, ‖(mertensFunction N : ℝ)‖ ≤ C * (N + 1 : ℝ) ^ r) :
    ∃ l : ℝ, Tendsto
      (fun N : ℕ => ∑ n ∈ Finset.range N,
        ((n + 1 : ℝ) ^ (-(s - a))) •
          (((n + 1 : ℝ) ^ (-a)) • (moebius (n + 1) : ℝ))) atTop (𝓝 l) := by
  have ha : 0 < a := lt_of_le_of_lt hr hra
  obtain ⟨B, hA⟩ := mobius_weighted_prefix_bounded_of_mertens_growth hr hra ha hC hM
  exact mobius_ordered_series_tendsto_of_bounded_weighted_prefix has hA

private theorem uniform_mertens_power_bound_of_isBigO
    {r : ℝ} (hr : 0 ≤ r)
    (hO : IsBigO atTop (fun N : ℕ => (mertensFunction N : ℝ))
      (fun N : ℕ => (N : ℝ) ^ r)) :
    ∃ C, 0 ≤ C ∧ ∀ N, ‖(mertensFunction N : ℝ)‖ ≤ C * (N + 1 : ℝ) ^ r := by
  obtain ⟨c, hcpos, heventually⟩ := (isBigO_iff').1 hO
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.1 heventually
  let S : ℝ := ∑ n ∈ Finset.range N₀, ‖(mertensFunction n : ℝ)‖
  let C : ℝ := c + S
  have hSnonneg : 0 ≤ S := by
    dsimp [S]
    exact Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hCnonneg : 0 ≤ C := by
    dsimp [C]
    positivity
  have hpower_lower (N : ℕ) : 1 ≤ (N + 1 : ℝ) ^ r := by
    have hbase : (1 : ℝ) ≤ (N + 1 : ℝ) := by
      exact_mod_cast (Nat.le_add_left 1 N)
    simpa using (Real.rpow_le_rpow_of_exponent_le hbase hr)
  refine ⟨C, hCnonneg, ?_⟩
  intro N
  by_cases hsmall : N < N₀
  · have hterm : ‖(mertensFunction N : ℝ)‖ ≤ S := by
      dsimp [S]
      exact Finset.single_le_sum (fun n _ => abs_nonneg ((mertensFunction n : ℝ)))
        (Finset.mem_range.mpr hsmall)
    calc
      ‖(mertensFunction N : ℝ)‖ ≤ S := hterm
      _ ≤ C := by dsimp [C]; linarith [hcpos, hSnonneg]
      _ = C * 1 := by ring
      _ ≤ C * (N + 1 : ℝ) ^ r :=
        mul_le_mul_of_nonneg_left (hpower_lower N) hCnonneg
  · have hlarge : N₀ ≤ N := le_of_not_gt hsmall
    have hNbound := hN₀ N hlarge
    have hpow_nonneg : 0 ≤ (N : ℝ) ^ r := Real.rpow_nonneg (Nat.cast_nonneg N) r
    have hpow_norm : ‖(N : ℝ) ^ r‖ = (N : ℝ) ^ r := Real.norm_of_nonneg hpow_nonneg
    have hshift : (N : ℝ) ^ r ≤ (N + 1 : ℝ) ^ r := by
      apply Real.rpow_le_rpow (Nat.cast_nonneg N)
      · exact_mod_cast Nat.le_succ N
      · exact hr
    calc
      ‖(mertensFunction N : ℝ)‖ ≤ c * (N : ℝ) ^ r := by simpa [hpow_norm] using hNbound
      _ ≤ c * (N + 1 : ℝ) ^ r := mul_le_mul_of_nonneg_left hshift hcpos.le
      _ ≤ C * (N + 1 : ℝ) ^ r := by
        apply mul_le_mul_of_nonneg_right
        · dsimp [C]
          linarith [hSnonneg]
        · exact Real.rpow_nonneg (by positivity) r

/--
The structural square-root cancellation claim for the Mertens function.
M(N) = O(N^(1/2 + ε)) for all ε > 0.
This claim is known to be exactly equivalent to the Riemann Hypothesis (Distance 1 edge).
-/
def MertensSquareRootCancellation : Prop :=
  ∀ ε : ℝ, 0 < ε → IsBigO atTop (fun N : ℕ => (mertensFunction N : ℝ)) (fun N : ℕ => (N : ℝ) ^ ((1 : ℝ) / 2 + ε))

/-- Any exponent strictly above `1/2` in the Mertens cancellation estimate yields
an all-indices polynomial bound with the shifted base `N + 1`. -/
theorem mertens_growth_bound_of_square_root_cancellation
    (hSQ : MertensSquareRootCancellation) {r : ℝ}
    (hr : (1 : ℝ) / 2 < r) :
    ∃ C, 0 ≤ C ∧ ∀ N, ‖(mertensFunction N : ℝ)‖ ≤ C * (N + 1 : ℝ) ^ r := by
  let ε : ℝ := r - (1 : ℝ) / 2
  have hε : 0 < ε := by dsimp [ε]; linarith
  have hO : IsBigO atTop
      (fun N : ℕ => (mertensFunction N : ℝ))
      (fun N : ℕ => (N : ℝ) ^ r) := by
    simpa [ε, show (1 : ℝ) / 2 + (r - (1 : ℝ) / 2) = r by ring] using hSQ ε hε
  exact uniform_mertens_power_bound_of_isBigO
    (le_of_lt (lt_trans (by norm_num : (0 : ℝ) < (1 : ℝ) / 2) hr)) hO

/-- If the square-root-cancellation estimate holds, the ordered real Möbius
series converges at every exponent strictly to the right of `1/2`. -/
theorem mobius_ordered_series_tendsto_of_square_root_cancellation
    (hSQ : MertensSquareRootCancellation) {s : ℝ}
    (hs : (1 : ℝ) / 2 < s) :
    ∃ l : ℝ, Tendsto
      (fun N : ℕ => ∑ n ∈ Finset.range N,
        ((n + 1 : ℝ) ^ (-s)) • (moebius (n + 1) : ℝ)) atTop (𝓝 l) := by
  let r : ℝ := ((1 : ℝ) / 2 + s) / 2
  let a : ℝ := (r + s) / 2
  have hrhalf : (1 : ℝ) / 2 < r := by dsimp [r]; linarith [hs]
  have hrs : r < s := by dsimp [r]; linarith [hs]
  have hra : r < a := by dsimp [a]; linarith [hrs]
  have has : a < s := by dsimp [a]; linarith [hrs]
  have hrnonneg : 0 ≤ r := le_of_lt (lt_trans (by norm_num) hrhalf)
  obtain ⟨C, hC, hM⟩ := mertens_growth_bound_of_square_root_cancellation hSQ hrhalf
  obtain ⟨l, hNested⟩ :=
    mobius_ordered_series_tendsto_of_mertens_growth hrnonneg hra has hC hM
  have hseq (N : ℕ) :
      (∑ n ∈ Finset.range N,
        ((n + 1 : ℝ) ^ (-(s - a))) •
          (((n + 1 : ℝ) ^ (-a)) • (moebius (n + 1) : ℝ))) =
      ∑ n ∈ Finset.range N, ((n + 1 : ℝ) ^ (-s)) • (moebius (n + 1) : ℝ) := by
    simp only [smul_eq_mul]
    apply Finset.sum_congr rfl
    intro n hn
    rw [← mul_assoc, ← Real.rpow_add (by positivity : 0 < (n + 1 : ℝ))
      (-(s - a)) (-a)]
    congr 1
    ring
  refine ⟨l, ?_⟩
  simpa only [hseq] using hNested

end InfoGeometry.Arithmetic.MobiusMertensRHEquivalence
