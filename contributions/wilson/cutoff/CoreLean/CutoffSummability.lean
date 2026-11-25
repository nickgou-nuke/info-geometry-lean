/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
/-
Released under Apache 2.0 license; see LICENSE-InfoGeometry-Apache-2.0.
-/
module

public import Mathlib.Analysis.Asymptotics.Lemmas
public import Mathlib.Analysis.PSeries
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

set_option linter.style.header.license
  "Released under Apache 2.0 license; see LICENSE-InfoGeometry-Apache-2.0." in
/-!
# Summability of the continuum-cutoff remainder

Section 11 of `WILSON_LOOPS_CONTINUUM_LIMIT.tex` uses
`μ_K = K^(3-κ/2) * log (b*K + gbar⁻²)^p` and occasionally loses a factor `K`.
These theorems establish both summability assertions, rather than assuming a
summable increment certificate. The offset `c` stands for the positive
quantity `gbar⁻²`; the general result only needs `0 ≤ c`.

The proof first bounds the affine logarithm by a logarithm at infinity, then
absorbs its fixed nonnegative real power into an arbitrarily small positive
real power. Native Mathlib p-series comparison finishes the argument. The
real log exponent covers `4*r + 2*p0` without an integrality assumption on
the manuscript's threshold exponent `p0`.
-/

@[expose] public section

noncomputable section

open Filter Asymptotics
open scoped Topology

namespace CoreLean.CutoffSummability

/-- A positive affine change of variable preserves the logarithmic growth
bound at positive infinity. -/
theorem log_affine_isBigO_log {b c : ℝ} (hb : 0 < b) (hc : 0 ≤ c) :
    (fun x : ℝ => Real.log (b * x + c)) =O[atTop] Real.log := by
  let C : ℝ := b + c + 1
  have hlim : Tendsto (fun x : ℝ => b * x + c) atTop atTop :=
    tendsto_atTop_add_const_right _ c (tendsto_id.const_mul_atTop hb)
  have hcmp : (fun x : ℝ => Real.log (b * x + c)) =O[atTop]
      (fun x : ℝ => Real.log (C * x)) := by
    apply IsBigO.of_bound'
    filter_upwards [eventually_ge_atTop (1 : ℝ), hlim.eventually_ge_atTop 1]
      with x hx harg
    have hcx : c ≤ c * x := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hx hc
    have hinput : b * x + c ≤ C * x := by
      dsimp [C]
      nlinarith
    rw [Real.norm_of_nonneg (Real.log_nonneg harg),
      Real.norm_of_nonneg (Real.log_nonneg (harg.trans hinput))]
    exact Real.log_le_log (lt_of_lt_of_le zero_lt_one harg) hinput
  exact hcmp.trans (Real.isBigO_log_const_mul_log_atTop C)

/-- Every fixed nonnegative real log power is absorbed by any strictly positive
power at infinity, including after a positive affine change of variable. -/
theorem log_affine_rpow_isBigO_rpow {b c δ : ℝ}
    (hb : 0 < b) (hc : 0 ≤ c) (hδ : 0 < δ) (p : ℝ) (hp : 0 ≤ p) :
    (fun x : ℝ => (Real.log (b * x + c)) ^ p) =O[atTop]
      (fun x : ℝ => x ^ δ) := by
  have hlog_nonneg : (0 : ℝ → ℝ) ≤ᶠ[atTop] Real.log := by
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
    exact Real.log_nonneg hx
  exact (IsBigO.rpow hp hlog_nonneg (log_affine_isBigO_log hb hc)).trans
    (isLittleO_log_rpow_rpow_atTop p hδ).isBigO

/-- Natural log powers are a specialization of the real-exponent bound. -/
theorem log_affine_pow_isBigO_rpow {b c δ : ℝ}
    (hb : 0 < b) (hc : 0 ≤ c) (hδ : 0 < δ) (p : ℕ) :
    (fun x : ℝ => (Real.log (b * x + c)) ^ p) =O[atTop]
      (fun x : ℝ => x ^ δ) := by
  simpa only [Real.rpow_natCast] using
    log_affine_rpow_isBigO_rpow hb hc hδ (p : ℝ) (Nat.cast_nonneg p)

/-- A real power strictly below `-1` remains summable after multiplication
by any fixed nonnegative real power of the affine logarithm. -/
theorem summable_rpow_mul_log_affine_rpow {a b c : ℝ}
    (ha : a < -1) (hb : 0 < b) (hc : 0 ≤ c) (p : ℝ) (hp : 0 ≤ p) :
    Summable (fun k : ℕ => (k : ℝ) ^ a * (Real.log (b * k + c)) ^ p) := by
  let δ : ℝ := (-1 - a) / 2
  have hδ : 0 < δ := by dsimp [δ]; linarith
  have hexp : a + δ < -1 := by dsimp [δ]; linarith
  have hprod : (fun x : ℝ => x ^ a * (Real.log (b * x + c)) ^ p) =O[atTop]
      (fun x : ℝ => x ^ (a + δ)) := by
    have h := (isBigO_refl (fun x : ℝ => x ^ a) atTop).mul
      (log_affine_rpow_isBigO_rpow hb hc hδ p hp)
    refine h.congr' Filter.EventuallyEq.rfl ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    exact (Real.rpow_add hx a δ).symm
  exact summable_of_isBigO_nat (Real.summable_nat_rpow.mpr hexp)
    (hprod.comp_tendsto tendsto_natCast_atTop_atTop)

/-- Natural log powers remain available as a convenient specialization. -/
theorem summable_rpow_mul_log_affine_pow {a b c : ℝ}
    (ha : a < -1) (hb : 0 < b) (hc : 0 ≤ c) (p : ℕ) :
    Summable (fun k : ℕ => (k : ℝ) ^ a * (Real.log (b * k + c)) ^ p) := by
  simpa only [Real.rpow_natCast] using
    summable_rpow_mul_log_affine_rpow ha hb hc (p : ℝ) (Nat.cast_nonneg p)

/-- The manuscript's `κ ≥ 13` condition makes the cutoff remainder
summable for every fixed nonnegative real log exponent. The proof needs
only `κ > 8`. -/
theorem summable_cutoff_remainder {κ b c : ℝ}
    (hκ : 13 ≤ κ) (hb : 0 < b) (hc : 0 ≤ c) (p : ℝ) (hp : 0 ≤ p) :
    Summable (fun k : ℕ =>
      (k : ℝ) ^ (3 - κ / 2) * (Real.log (b * k + c)) ^ p) := by
  exact summable_rpow_mul_log_affine_rpow (by linarith) hb hc p hp

/-- The remainder remains summable after a full linear loss in `K`.
This is the loss appearing when the final observable estimate sums over
scales. The proof needs only `κ > 10`, so `κ ≥ 13` has a strict margin. -/
theorem summable_cutoff_remainder_mul_cutoff {κ b c : ℝ}
    (hκ : 13 ≤ κ) (hb : 0 < b) (hc : 0 ≤ c) (p : ℝ) (hp : 0 ≤ p) :
    Summable (fun k : ℕ => (k : ℝ) *
      ((k : ℝ) ^ (3 - κ / 2) * (Real.log (b * k + c)) ^ p)) := by
  have hs : Summable (fun k : ℕ =>
      (k : ℝ) ^ (4 - κ / 2) * (Real.log (b * k + c)) ^ p) :=
    summable_rpow_mul_log_affine_rpow (by linarith) hb hc p hp
  apply hs.congr_cofinite
  rw [Nat.cofinite_eq_atTop]
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with k hk
  have hk' : 0 < (k : ℝ) := Nat.cast_pos.mpr hk
  rw [show 4 - κ / 2 = (3 - κ / 2) + 1 by ring,
    Real.rpow_add_one hk'.ne']
  ring

end CoreLean.CutoffSummability
