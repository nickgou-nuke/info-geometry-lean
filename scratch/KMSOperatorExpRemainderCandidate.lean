/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib

/-!
# Operator exponential: exact quadratic-tail candidate

This candidate works in the actual normed algebra of continuous endomorphisms
of a complete real normed space.  It proves an exact power-series expression
for the exponential remainder after its constant and linear terms.  It does
not yet claim a sharp Dikin/KMS norm bound for that tail.
-/

set_option autoImplicit false

noncomputable section

namespace InfoGeometry.Canonical.KMSOperatorExpRemainderCandidate

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]

local notation "EndH" => H →L[ℝ] H

/-- The second-order tail of the exponential series in the continuous
endomorphism algebra. -/
def expSecondOrderTail (A : EndH) : EndH :=
  ∑' n : ℕ, ((Nat.factorial (n + 2) : ℝ)⁻¹) • A ^ (n + 2)

/-- The operator exponential remainder is exactly its series tail starting
at degree two.  This remains a genuinely noncommutative operator statement;
no scalar or matrix representation is introduced. -/
theorem exp_sub_one_sub_eq_secondOrderTail (A : EndH) :
    NormedSpace.exp A - 1 - A = expSecondOrderTail A := by
  let f : ℕ → EndH := fun n => ((Nat.factorial n : ℝ)⁻¹) • A ^ n
  have hs : HasSum f (NormedSpace.exp A) := by
    simpa only [f] using NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) A
  have hsplit := hs.summable.sum_add_tsum_nat_add 2
  have hprefix : (∑ n ∈ Finset.range 2, f n) = (1 : EndH) + A := by
    calc
      (∑ n ∈ Finset.range 2, f n) = f 0 + f 1 := by
        rw [Finset.sum_range_succ, Finset.sum_range_succ]
        simp
      _ = (1 : EndH) + A := by simp [f]
  have htail : (∑' n : ℕ, f (n + 2)) = expSecondOrderTail A := by
    apply tsum_congr
    intro n
    simp [f]
  rw [hs.tsum_eq] at hsplit
  rw [hprefix, htail] at hsplit
  dsimp [expSecondOrderTail] at hsplit ⊢
  rw [← hsplit]
  abel

/-- The operator exponential remainder has a quadratic norm bound on the
unit ball.  This candidate uses the genuine continuous-endomorphism algebra
and bounds its degree-two-and-higher series by a geometric majorant. -/
theorem norm_exp_sub_one_sub_le_sq (A : EndH) (hA : ‖A‖ ≤ 1) :
    ‖NormedSpace.exp A - 1 - A‖ ≤ ‖A‖ ^ 2 := by
  rw [exp_sub_one_sub_eq_secondOrderTail]
  let r : ℝ := ‖A‖
  let F : ℝ := (Nat.factorial 2 : ℝ)
  let q : ℝ := (3 : ℝ)⁻¹
  let term : ℕ → EndH := fun n =>
    ((Nat.factorial (n + 2) : ℝ)⁻¹) • A ^ (n + 2)
  have hr_nonneg : 0 ≤ r := norm_nonneg A
  have hr_le : r ≤ 1 := hA
  have hF : F = 2 := by norm_num [F, Nat.factorial]
  have hgeom : Summable (fun n : ℕ => F⁻¹ * q ^ n) := by
    simpa [q] using
      (summable_geometric_of_lt_one (r := q)
        (by norm_num [q] : 0 ≤ q)
        (by norm_num [q] : q < 1)).mul_left (F⁻¹)
  have hgeom_sum : (∑' n : ℕ, q ^ n) = 3 / 2 := by
    rw [tsum_geometric_of_lt_one (r := q)
      (by norm_num [q] : 0 ≤ q)
      (by norm_num [q] : q < 1)]
    norm_num [q]
  have hmajorant : Summable (fun n : ℕ => r ^ 2 * (F⁻¹ * q ^ n)) :=
    hgeom.mul_left (r ^ 2)
  have htail_norm : Summable (fun n : ℕ =>
      ‖((Nat.factorial (n + 2) : ℝ)⁻¹) • A ^ (n + 2)‖) := by
    have h := NormedSpace.norm_expSeries_summable' (𝕂 := ℝ) A
    have hi : Function.Injective (fun n : ℕ => n + 2) := by
      intro n m hnm
      exact Nat.add_right_cancel hnm
    have h' := h.comp_injective hi
    exact h'.congr (fun n => by rfl)
  have hterm (n : ℕ) : ‖term n‖ ≤ r ^ 2 * (F⁻¹ * q ^ n) := by
    have hfacNat : Nat.factorial 2 * 3 ^ n ≤ Nat.factorial (n + 2) := by
      simpa [Nat.add_comm] using
        (Nat.factorial_mul_pow_le_factorial (m := 2) (n := n))
    have hfac : F * (3 : ℝ) ^ n ≤ (Nat.factorial (n + 2) : ℝ) := by
      change (Nat.factorial 2 : ℝ) * (3 : ℝ) ^ n ≤ _
      exact_mod_cast hfacNat
    have hfac_pos : 0 < (Nat.factorial (n + 2) : ℝ) := by positivity
    have hbase_pos : 0 < F * (3 : ℝ) ^ n := by rw [hF]; positivity
    have hinv : (Nat.factorial (n + 2) : ℝ)⁻¹ ≤ (F * (3 : ℝ) ^ n)⁻¹ := by
      simpa [one_div] using one_div_le_one_div_of_le hbase_pos hfac
    have hrpow : r ^ (n + 2) ≤ r ^ 2 := by
      rw [pow_add]
      calc
        r ^ n * r ^ 2 ≤ 1 * r ^ 2 :=
          mul_le_mul_of_nonneg_right (pow_le_one₀ hr_nonneg hr_le) (sq_nonneg r)
        _ = r ^ 2 := by ring
    have hcoef : (F * (3 : ℝ) ^ n)⁻¹ = F⁻¹ * q ^ n := by
      calc
        (F * (3 : ℝ) ^ n)⁻¹ = F⁻¹ * ((3 : ℝ)⁻¹) ^ n := by
          rw [mul_inv, inv_pow]
        _ = F⁻¹ * q ^ n := rfl
    have hcoeff : 0 ≤ (Nat.factorial (n + 2) : ℝ)⁻¹ :=
      inv_nonneg.mpr (Nat.cast_nonneg _)
    calc
      ‖term n‖ = |(Nat.factorial (n + 2) : ℝ)⁻¹| * ‖A ^ (n + 2)‖ := by
        dsimp [term]
        rw [norm_smul, Real.norm_eq_abs]
      _ = (Nat.factorial (n + 2) : ℝ)⁻¹ * ‖A ^ (n + 2)‖ := by
        rw [abs_of_nonneg hcoeff]
      _ ≤ (Nat.factorial (n + 2) : ℝ)⁻¹ * r ^ (n + 2) :=
        mul_le_mul_of_nonneg_left
          (norm_pow_le' A (by omega : 0 < n + 2))
          (inv_nonneg.mpr hfac_pos.le)
      _ ≤ (Nat.factorial (n + 2) : ℝ)⁻¹ * r ^ 2 :=
        mul_le_mul_of_nonneg_left hrpow (inv_nonneg.mpr hfac_pos.le)
      _ ≤ ((F * (3 : ℝ) ^ n)⁻¹) * r ^ 2 :=
        mul_le_mul_of_nonneg_right hinv (sq_nonneg r)
      _ = r ^ 2 * (F⁻¹ * q ^ n) := by rw [hcoef]; ring
  calc
    ‖expSecondOrderTail A‖ ≤ ∑' n : ℕ, ‖term n‖ := by
      simpa [expSecondOrderTail, term] using norm_tsum_le_tsum_norm htail_norm
    _ ≤ ∑' n : ℕ, r ^ 2 * (F⁻¹ * q ^ n) :=
      Summable.tsum_le_tsum hterm htail_norm hmajorant
    _ = r ^ 2 * (F⁻¹ * (∑' n : ℕ, ((3 : ℝ)⁻¹) ^ n)) := by
      calc
        (∑' n : ℕ, r ^ 2 * (F⁻¹ * q ^ n))
            = r ^ 2 * ∑' n : ℕ, F⁻¹ * q ^ n := by rw [tsum_mul_left]
        _ = r ^ 2 * (F⁻¹ * ∑' n : ℕ, q ^ n) := by rw [tsum_mul_left]
    _ = r ^ 2 * (3 / 4) := by rw [hgeom_sum, hF]; norm_num
    _ ≤ r ^ 2 := by
      have hsq : 0 ≤ r ^ 2 := sq_nonneg r
      nlinarith

end InfoGeometry.Canonical.KMSOperatorExpRemainderCandidate
