/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Analysis.DikinWeylBoundedness
import InfoGeometry.Arithmetic.MertensMellinRiemannHypothesis

/-!
# Actual Mertens sums in prescribed Dikin scales

The native Möbius coefficients give the unconditional estimate `|M(N)| ≤ N`.
Consequently the actual Mertens sum lies strictly inside the logarithmic
Dikin unit bound at base scale `N+1`.

At the prescribed scales `(N+1)^(1/2+ε)`, boundedness of the quadratic ratios
is exactly the existing square-root-cancellation proposition. The equivalence
is proved in both directions and feeds the native Mellin-to-RH theorem.
Boundedness at those smaller scales remains an arithmetic hypothesis; freely
choosing a larger scale does not discharge it.
-/

noncomputable section

namespace InfoGeometry.Arithmetic.MertensDikinBounds

open ArithmeticFunction Asymptotics Filter
open scoped ArithmeticFunction.Moebius Topology
open MobiusMertensRHEquivalence
open InfoGeometry.Analysis.DikinWeylBoundedness
open InfoGeometry.InformationGeometry.BurgStein

/-- The actual native Möbius sum has the unconditional linear bound, including `N=0`. -/
theorem norm_mertensFunction_le (N : ℕ) :
    ‖(mertensFunction N : ℝ)‖ ≤ (N : ℝ) := by
  induction N with
  | zero => simp [mertensFunction_zero]
  | succ N ih =>
    have hmu : ‖(μ (N + 1) : ℝ)‖ ≤ 1 := by
      rw [Real.norm_eq_abs]
      exact_mod_cast (abs_moebius_le_one (n := N + 1))
    rw [mertensFunction_succ, Int.cast_add, Nat.cast_add, Nat.cast_one]
    exact (norm_add_le _ _).trans (add_le_add ih hmu)

/-- Linear Weyl scale gives a strict unit Dikin bound without a cancellation assumption. -/
theorem mertens_fisherScaleMetric_linear_lt_one (N : ℕ) :
    fisherScaleMetric ((N : ℝ) + 1) (mertensFunction N : ℝ) < 1 := by
  have hx : 0 < (N : ℝ) + 1 := by positivity
  have h := norm_mertensFunction_le N
  rw [Real.norm_eq_abs] at h
  have hbound : |(mertensFunction N : ℝ)| < 1 * ((N : ℝ) + 1) := by linarith
  simpa only [one_pow] using
    (fisherScaleMetric_lt_sq_iff hx (by norm_num : (0 : ℝ) < 1)).mpr hbound

/-- Every exponent at least one already gives an unconditional uniform quadratic bound. -/
theorem mertens_fisherScaleMetric_power_le_one {r : ℝ} (hr : 1 ≤ r) (N : ℕ) :
    fisherScaleMetric (((N : ℝ) + 1) ^ r) (mertensFunction N : ℝ) ≤ 1 := by
  have hx : 0 < ((N : ℝ) + 1) ^ r := Real.rpow_pos_of_pos (by positivity) r
  have hbase : (1 : ℝ) ≤ (N : ℝ) + 1 := by
    linarith [(Nat.cast_nonneg N : (0 : ℝ) ≤ (N : ℝ))]
  have hp : (N : ℝ) + 1 ≤ ((N : ℝ) + 1) ^ r := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hbase hr
  have hbound : |(mertensFunction N : ℝ)| ≤ 1 * (((N : ℝ) + 1) ^ r) := by
    rw [one_mul]
    have hM : |(mertensFunction N : ℝ)| ≤ (N : ℝ) := by
      simpa only [Real.norm_eq_abs] using norm_mertensFunction_le N
    exact hM.trans ((by linarith : (N : ℝ) ≤ (N : ℝ) + 1).trans hp)
  simpa only [one_pow] using
    (fisherScaleMetric_le_sq_iff hx (by norm_num : (0 : ℝ) ≤ 1)).mpr hbound

/-- Recover the original unshifted asymptotic power bound, including the factor `2^r`. -/
theorem isBigO_mertens_of_shifted_power_bound {r C : ℝ}
    (hr : 0 ≤ r) (hC : 0 ≤ C)
    (hM : ∀ N : ℕ, |(mertensFunction N : ℝ)| ≤ C * ((N : ℝ) + 1) ^ r) :
    IsBigO atTop (fun N : ℕ => (mertensFunction N : ℝ))
      (fun N : ℕ => (N : ℝ) ^ r) := by
  apply IsBigO.of_bound (C * (2 : ℝ) ^ r)
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hNreal : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hp : ((N : ℝ) + 1) ^ r ≤ (2 : ℝ) ^ r * (N : ℝ) ^ r := by
    calc
      ((N : ℝ) + 1) ^ r ≤ (2 * (N : ℝ)) ^ r :=
        Real.rpow_le_rpow (by positivity) (by linarith) hr
      _ = (2 : ℝ) ^ r * (N : ℝ) ^ r := Real.mul_rpow (by norm_num) (by positivity)
  rw [Real.norm_eq_abs, Real.norm_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg N) r)]
  calc
    |(mertensFunction N : ℝ)| ≤ C * ((N : ℝ) + 1) ^ r := hM N
    _ ≤ C * ((2 : ℝ) ^ r * (N : ℝ) ^ r) := mul_le_mul_of_nonneg_left hp hC
    _ = (C * (2 : ℝ) ^ r) * (N : ℝ) ^ r := (mul_assoc _ _ _).symm

/-- The arithmetic cancellation premise is equivalent to bounded Dikin quadratics at
the prescribed near-square-root scales; the scale is not chosen from the observed sum. -/
theorem mertensSquareRootCancellation_iff_bddAbove_dikin :
    MertensSquareRootCancellation ↔
      ∀ ε : ℝ, 0 < ε →
        BddAbove (Set.range fun N : ℕ =>
          fisherScaleMetric (((N : ℝ) + 1) ^ ((1 : ℝ) / 2 + ε))
            (mertensFunction N : ℝ)) := by
  constructor
  · intro hM ε hε
    apply (bddAbove_fisherScaleMetric_range_iff _ _
      (fun N => Real.rpow_pos_of_pos (by positivity) _)).mpr
    obtain ⟨C, hC, hbound⟩ := mertens_growth_bound_of_square_root_cancellation hM
      (show (1 : ℝ) / 2 < (1 : ℝ) / 2 + ε by linarith)
    exact ⟨C, hC, fun N => by simpa only [Real.norm_eq_abs] using hbound N⟩
  · intro h ε hε
    obtain ⟨C, hC, hbound⟩ := (bddAbove_fisherScaleMetric_range_iff _ _
      (fun N => Real.rpow_pos_of_pos (by positivity) _)).mp (h ε hε)
    exact isBigO_mertens_of_shifted_power_bound (by linarith) hC hbound

/-- Native RH follows from uniform quadratic boundedness at each prescribed scale.
The boundedness hypothesis is exactly characterized by the preceding equivalence. -/
theorem riemannHypothesis_of_bddAbove_dikin
    (h : ∀ ε : ℝ, 0 < ε →
      BddAbove (Set.range fun N : ℕ =>
        fisherScaleMetric (((N : ℝ) + 1) ^ ((1 : ℝ) / 2 + ε))
          (mertensFunction N : ℝ))) :
    _root_.RiemannHypothesis :=
  MertensMellinRiemannHypothesis.riemannHypothesis_of_mertensSquareRootCancellation
    (mertensSquareRootCancellation_iff_bddAbove_dikin.mpr h)

end InfoGeometry.Arithmetic.MertensDikinBounds
