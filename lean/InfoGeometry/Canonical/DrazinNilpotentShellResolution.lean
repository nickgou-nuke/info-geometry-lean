/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib.Tactic
import InfoGeometry.Canonical.DrazinNilpotentShell

/-!
# Drazin-dressed nilpotent shell resolution

Given a Drazin inverse `d` of index `k` for `a`, the complementary projector
`E_N = 1 - a d` cuts out the nilpotent part `N = a E_N`.  Dressing the raw
range and shell projectors of `N` by `E_N` produces two-sided shells

`P̂ m = E_N P_m E_N`,  `S m = E_N Q_m E_N = Q_m E_N`

which are idempotent, mutually orthogonal, orthogonal to the regular projector
`E_C = a d`, and satisfy `E_C + Σ_{m<k} S_m = 1`.  On the full operator `a`,
`S m * a^(m+1) = 0`; at degree `m` there is a recovery identity, equivalently
the zero test `X * S m * a^m = 0 ↔ X * S m = 0`.  This is a recovery statement
and does not assert that a shell is nonzero or that `k` is minimal.

All statements are over an arbitrary star ring.  No commutativity,
diagonalizability, symmetry of `E_N`, or finite dimensionality is assumed.
-/

namespace InfoGeometry.Canonical.DrazinNilpotentShell

open InfoGeometry.Canonical.Drazin
open InfoGeometry.Canonical.Drazin.IsDrazinInverse
open InfoGeometry.Canonical.MoorePenrose

variable {R : Type*} [Ring R] [StarRing R]

section Drazin

variable {a d : R} {k : ℕ}

/-- The dressed range projector `P̂ m = E_N * P_m * E_N`. -/
def drazinRangeProj (a d : R) (M : ℕ → R) (m : ℕ) : R :=
  complementaryProjection a d * rangeProj (fittingNilpotentPart a d) M m *
    complementaryProjection a d

/-- The dressed shell projector `S m = E_N * Q_m * E_N`. -/
def drazinShellProj (a d : R) (M : ℕ → R) (m : ℕ) : R :=
  complementaryProjection a d * shellProj (fittingNilpotentPart a d) M m *
    complementaryProjection a d

/-! ### Absorption of `E_N` into positive powers of the nilpotent part -/

theorem complementaryProjection_mul_fittingNilpotentPart
    (h : IsDrazinInverse a d k) :
    complementaryProjection a d * fittingNilpotentPart a d =
      fittingNilpotentPart a d := by
  unfold fittingNilpotentPart
  rw [← mul_assoc, complementaryProjection_comm_self h, mul_assoc,
    complementaryProjection_is_idempotent h]

theorem complementaryProjection_mul_fittingNilpotentPart_pow
    (h : IsDrazinInverse a d k) {m : ℕ} (hm : 1 ≤ m) :
    complementaryProjection a d * fittingNilpotentPart a d ^ m =
      fittingNilpotentPart a d ^ m := by
  cases m with
  | zero => omega
  | succ n =>
      rw [pow_succ', ← mul_assoc,
        complementaryProjection_mul_fittingNilpotentPart h]

theorem complementaryProjection_mul_fittingNilpotentPart_pow_eq
    (h : IsDrazinInverse a d k) (m : ℕ) :
    complementaryProjection a d * fittingNilpotentPart a d ^ m =
      a ^ m * complementaryProjection a d := by
  induction m with
  | zero => simp
  | succ m ih =>
      calc
        complementaryProjection a d * fittingNilpotentPart a d ^ (m + 1)
            = (complementaryProjection a d * fittingNilpotentPart a d) *
                fittingNilpotentPart a d ^ m := by rw [pow_succ', ← mul_assoc]
        _ = fittingNilpotentPart a d * fittingNilpotentPart a d ^ m := by
              rw [complementaryProjection_mul_fittingNilpotentPart h]
        _ = (a * complementaryProjection a d) *
                fittingNilpotentPart a d ^ m := rfl
        _ = a * (complementaryProjection a d *
                fittingNilpotentPart a d ^ m) := by rw [mul_assoc]
        _ = a * (a ^ m * complementaryProjection a d) := by rw [ih]
        _ = (a * a ^ m) * complementaryProjection a d := by rw [← mul_assoc]
        _ = a ^ (m + 1) * complementaryProjection a d := by rw [← pow_succ']

theorem pow_mul_complementaryProjection_comm (h : IsDrazinInverse a d k) (m : ℕ) :
    a ^ m * complementaryProjection a d =
      complementaryProjection a d * a ^ m :=
  ((show Commute a (complementaryProjection a d) from
      (complementaryProjection_comm_self h).symm).pow_left m).eq

theorem complementaryProjection_mul_pow_eq (h : IsDrazinInverse a d k) (m : ℕ) :
    complementaryProjection a d * a ^ m =
      complementaryProjection a d * fittingNilpotentPart a d ^ m := by
  rw [complementaryProjection_mul_fittingNilpotentPart_pow_eq h m,
    pow_mul_complementaryProjection_comm h m]

theorem complementaryProjection_mul_pow_eq_fittingNilpotentPart_pow
    (h : IsDrazinInverse a d k) {m : ℕ} (hm : 1 ≤ m) :
    complementaryProjection a d * a ^ m = fittingNilpotentPart a d ^ m := by
  rw [complementaryProjection_mul_pow_eq h m,
    complementaryProjection_mul_fittingNilpotentPart_pow h hm]

theorem complementaryProjection_mul_fittingNilpotentPart_pow_k
    (h : IsDrazinInverse a d k) :
    complementaryProjection a d * fittingNilpotentPart a d ^ k = 0 := by
  rw [complementaryProjection_mul_fittingNilpotentPart_pow_eq h k,
    power_mul_complementaryProjection_eq_zero h]

theorem fittingNilpotentPart_pow_k_eq_zero (h : IsDrazinInverse a d k)
    (hk : 1 ≤ k) :
    fittingNilpotentPart a d ^ k = 0 := by
  rw [← complementaryProjection_mul_fittingNilpotentPart_pow h hk,
    complementaryProjection_mul_fittingNilpotentPart_pow_k h]

theorem complementaryProjection_mul_rangeProj_of_one_le
    (h : IsDrazinInverse a d k) (M : ℕ → R) {m : ℕ} (hm : 1 ≤ m) :
    complementaryProjection a d * rangeProj (fittingNilpotentPart a d) M m =
      rangeProj (fittingNilpotentPart a d) M m := by
  unfold rangeProj
  rw [← mul_assoc, complementaryProjection_mul_fittingNilpotentPart_pow h hm]

theorem complementaryProjection_mul_shellProj_of_one_le
    (h : IsDrazinInverse a d k) (M : ℕ → R) {m : ℕ} (hm : 1 ≤ m) :
    complementaryProjection a d * shellProj (fittingNilpotentPart a d) M m =
      shellProj (fittingNilpotentPart a d) M m := by
  have hm1 : 1 ≤ m + 1 := le_trans hm (Nat.le_succ m)
  unfold shellProj
  rw [mul_sub,
    complementaryProjection_mul_rangeProj_of_one_le h M hm,
    complementaryProjection_mul_rangeProj_of_one_le h M hm1]

/-! ### The dressed range projector is `P_m * E_N` on positive indices -/

theorem drazinRangeProj_eq_rangeProj_mul_of_one_le (h : IsDrazinInverse a d k)
    {M : ℕ → R} (hM : PowerMPFamily (fittingNilpotentPart a d) M) {r : ℕ}
    (hr : 1 ≤ r) :
    drazinRangeProj a d M r =
      rangeProj (fittingNilpotentPart a d) M r * complementaryProjection a d := by
  unfold drazinRangeProj
  rw [complementaryProjection_mul_rangeProj_of_one_le h M hr]

/-- Universal absorption law for dressed range projectors, with no symmetry
assumption on `E_N`. -/
theorem drazinRangeProj_mul_of_le (h : IsDrazinInverse a d k) {M : ℕ → R}
    (hM : PowerMPFamily (fittingNilpotentPart a d) M) {p q : ℕ} (hpq : p ≤ q) :
    drazinRangeProj a d M p * drazinRangeProj a d M q =
      drazinRangeProj a d M q := by
  rcases Nat.eq_zero_or_pos q with hq | hq
  · rw [hq] at hpq ⊢
    have hp : p = 0 := Nat.le_zero.mp hpq
    rw [hp]
    unfold drazinRangeProj
    rw [rangeProj_zero hM, mul_one, complementaryProjection_is_idempotent h,
      complementaryProjection_is_idempotent h]
  · have hq1 : 1 ≤ q := Nat.succ_le_of_lt hq
    rcases Nat.eq_zero_or_pos p with hp | hp
    · rw [hp, drazinRangeProj_eq_rangeProj_mul_of_one_le h hM hq1]
      unfold drazinRangeProj
      rw [rangeProj_zero hM, mul_one, complementaryProjection_is_idempotent h,
        ← mul_assoc, complementaryProjection_mul_rangeProj_of_one_le h M hq1]
    · have hp1 : 1 ≤ p := Nat.succ_le_of_lt hp
      rw [drazinRangeProj_eq_rangeProj_mul_of_one_le h hM hp1,
        drazinRangeProj_eq_rangeProj_mul_of_one_le h hM hq1]
      calc
        (rangeProj (fittingNilpotentPart a d) M p * complementaryProjection a d) *
            (rangeProj (fittingNilpotentPart a d) M q * complementaryProjection a d)
            = rangeProj (fittingNilpotentPart a d) M p *
                (complementaryProjection a d *
                  rangeProj (fittingNilpotentPart a d) M q) *
                complementaryProjection a d := by simp only [mul_assoc]
        _ = rangeProj (fittingNilpotentPart a d) M p *
                rangeProj (fittingNilpotentPart a d) M q *
                complementaryProjection a d := by
              rw [complementaryProjection_mul_rangeProj_of_one_le h M hq1]
        _ = rangeProj (fittingNilpotentPart a d) M q *
                complementaryProjection a d := by
              rw [rangeProj_mul_of_le hM hpq]

/-- Reverse absorption law for dressed range projectors. -/
theorem drazinRangeProj_mul_of_ge (h : IsDrazinInverse a d k) {M : ℕ → R}
    (hM : PowerMPFamily (fittingNilpotentPart a d) M) {p q : ℕ} (hpq : p ≤ q) :
    drazinRangeProj a d M q * drazinRangeProj a d M p =
      drazinRangeProj a d M q := by
  rcases Nat.eq_zero_or_pos p with hp | hp
  · rw [hp]
    rcases Nat.eq_zero_or_pos q with hq | hq
    · rw [hq]
      unfold drazinRangeProj
      rw [rangeProj_zero hM, mul_one, complementaryProjection_is_idempotent h,
        complementaryProjection_is_idempotent h]
    · have hq1 : 1 ≤ q := Nat.succ_le_of_lt hq
      calc
        drazinRangeProj a d M q * drazinRangeProj a d M 0
            = drazinRangeProj a d M q * complementaryProjection a d := by
                unfold drazinRangeProj
                rw [rangeProj_zero hM, mul_one,
                  complementaryProjection_is_idempotent h]
        _ = drazinRangeProj a d M q := by
                rw [drazinRangeProj_eq_rangeProj_mul_of_one_le h hM hq1,
                  mul_assoc, complementaryProjection_is_idempotent h]
  · have hp1 : 1 ≤ p := Nat.succ_le_of_lt hp
    have hq1 : 1 ≤ q := le_trans hp1 hpq
    rw [drazinRangeProj_eq_rangeProj_mul_of_one_le h hM hq1,
      drazinRangeProj_eq_rangeProj_mul_of_one_le h hM hp1]
    calc
      (rangeProj (fittingNilpotentPart a d) M q * complementaryProjection a d) *
          (rangeProj (fittingNilpotentPart a d) M p * complementaryProjection a d)
          = rangeProj (fittingNilpotentPart a d) M q *
              (complementaryProjection a d *
                rangeProj (fittingNilpotentPart a d) M p) *
              complementaryProjection a d := by simp only [mul_assoc]
      _ = rangeProj (fittingNilpotentPart a d) M q *
              rangeProj (fittingNilpotentPart a d) M p *
              complementaryProjection a d := by
            rw [complementaryProjection_mul_rangeProj_of_one_le h M hp1]
      _ = rangeProj (fittingNilpotentPart a d) M q *
              complementaryProjection a d := by
            rw [rangeProj_mul_of_ge hM hpq]

/-- Universal absorption law for dressed range projectors:
`P̂_a * P̂_b = P̂_(max a b)`, with no symmetry assumption on `E_N`. -/
theorem drazinRangeProj_mul (h : IsDrazinInverse a d k) {M : ℕ → R}
    (hM : PowerMPFamily (fittingNilpotentPart a d) M) (p q : ℕ) :
    drazinRangeProj a d M p * drazinRangeProj a d M q =
      drazinRangeProj a d M (max p q) := by
  rcases le_total p q with hpq | hqp
  · rw [max_eq_right hpq, drazinRangeProj_mul_of_le h hM hpq]
  · rw [max_eq_left hqp, drazinRangeProj_mul_of_ge h hM hqp]

/-! ### The dressed shells are `Q_m * E_N` -/

theorem drazinShellProj_eq_sub (a d : R) (M : ℕ → R) (m : ℕ) :
    drazinShellProj a d M m =
      drazinRangeProj a d M m - drazinRangeProj a d M (m + 1) := by
  unfold drazinShellProj drazinRangeProj shellProj
  rw [mul_sub, sub_mul]

theorem drazinShellProj_eq_right_mul (h : IsDrazinInverse a d k) {M : ℕ → R}
    (hM : PowerMPFamily (fittingNilpotentPart a d) M) (m : ℕ) :
    drazinShellProj a d M m =
      shellProj (fittingNilpotentPart a d) M m * complementaryProjection a d := by
  cases m with
  | zero =>
      unfold drazinShellProj shellProj
      rw [rangeProj_zero hM, mul_sub, sub_mul, sub_mul, mul_one, one_mul,
        complementaryProjection_is_idempotent h,
        complementaryProjection_mul_rangeProj_of_one_le h M (le_refl 1)]
  | succ r =>
      have hm1 : 1 ≤ r + 1 := Nat.succ_le_succ (Nat.zero_le r)
      have hm2 : 1 ≤ r + 2 := Nat.succ_le_succ (Nat.zero_le (r + 1))
      unfold drazinShellProj shellProj
      rw [mul_sub,
        complementaryProjection_mul_rangeProj_of_one_le h M hm1,
        complementaryProjection_mul_rangeProj_of_one_le h M hm2]

theorem rangeProj_mul_complementaryProjection_of_one_le (h : IsDrazinInverse a d k)
    {M : ℕ → R} (hM : PowerMPFamily (fittingNilpotentPart a d) M)
    (h_symm : star (complementaryProjection a d) = complementaryProjection a d)
    {r : ℕ} (hr : 1 ≤ r) :
    rangeProj (fittingNilpotentPart a d) M r * complementaryProjection a d =
      rangeProj (fittingNilpotentPart a d) M r := by
  calc
    rangeProj (fittingNilpotentPart a d) M r * complementaryProjection a d
        = star (rangeProj (fittingNilpotentPart a d) M r) *
            star (complementaryProjection a d) := by
          rw [rangeProj_symm hM r, h_symm]
    _ = star (complementaryProjection a d *
            rangeProj (fittingNilpotentPart a d) M r) := (star_mul _ _).symm
    _ = star (rangeProj (fittingNilpotentPart a d) M r) := by
          rw [complementaryProjection_mul_rangeProj_of_one_le h M hr]
    _ = rangeProj (fittingNilpotentPart a d) M r := rangeProj_symm hM r

/-- When `E_N` is self-adjoint (orthogonal core/nilpotent split), the dressed
shell is also the raw left product `E_N * Q_m`. -/
theorem drazinShellProj_eq_left_mul_of_symm (h : IsDrazinInverse a d k)
    {M : ℕ → R} (hM : PowerMPFamily (fittingNilpotentPart a d) M)
    (h_symm : star (complementaryProjection a d) = complementaryProjection a d)
    (m : ℕ) :
    drazinShellProj a d M m =
      complementaryProjection a d * shellProj (fittingNilpotentPart a d) M m := by
  cases m with
  | zero =>
      unfold drazinShellProj shellProj
      rw [rangeProj_zero hM, mul_sub, sub_mul, mul_one,
        complementaryProjection_is_idempotent h, mul_assoc,
        rangeProj_mul_complementaryProjection_of_one_le h hM h_symm (le_refl 1)]
  | succ r =>
      have hm1 : 1 ≤ r + 1 := Nat.succ_le_succ (Nat.zero_le r)
      have hm2 : 1 ≤ r + 2 := Nat.succ_le_succ (Nat.zero_le (r + 1))
      unfold drazinShellProj shellProj
      rw [mul_assoc, sub_mul,
        rangeProj_mul_complementaryProjection_of_one_le h hM h_symm hm1,
        rangeProj_mul_complementaryProjection_of_one_le h hM h_symm hm2]

/-! ### Idempotence, orthogonality, and partition of unity -/

theorem drazinShellProj_idem (h : IsDrazinInverse a d k) {M : ℕ → R}
    (hM : PowerMPFamily (fittingNilpotentPart a d) M) (m : ℕ) :
    drazinShellProj a d M m * drazinShellProj a d M m =
      drazinShellProj a d M m := by
  rw [drazinShellProj_eq_sub, sub_mul, mul_sub, mul_sub,
    drazinRangeProj_mul_of_le h hM (le_refl m),
    drazinRangeProj_mul_of_le h hM (Nat.le_succ m),
    drazinRangeProj_mul_of_ge h hM (Nat.le_succ m),
    drazinRangeProj_mul_of_le h hM (le_refl (m + 1))]
  abel

theorem drazinShellProj_orthogonal (h : IsDrazinInverse a d k) {M : ℕ → R}
    (hM : PowerMPFamily (fittingNilpotentPart a d) M) {m r : ℕ} (hne : m ≠ r) :
    drazinShellProj a d M m * drazinShellProj a d M r = 0 := by
  rw [drazinShellProj_eq_sub a d M m, drazinShellProj_eq_sub a d M r,
    sub_mul, mul_sub, mul_sub]
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · rw [drazinRangeProj_mul_of_le h hM (le_of_lt hlt),
      drazinRangeProj_mul_of_le h hM (le_of_lt (Nat.lt_succ_of_lt hlt)),
      drazinRangeProj_mul_of_le h hM (Nat.succ_le_of_lt hlt),
      drazinRangeProj_mul_of_le h hM
        (le_trans (Nat.succ_le_of_lt hlt) (Nat.le_succ r))]
    abel
  · rw [drazinRangeProj_mul_of_ge h hM (le_of_lt hgt),
      drazinRangeProj_mul_of_ge h hM (Nat.succ_le_of_lt hgt),
      drazinRangeProj_mul_of_ge h hM (le_of_lt (Nat.lt_succ_of_lt hgt)),
      drazinRangeProj_mul_of_ge h hM
        (le_trans (Nat.succ_le_of_lt hgt) (Nat.le_succ m))]
    abel

theorem projection_drazinShellProj_orthogonal (h : IsDrazinInverse a d k)
    (M : ℕ → R) (m : ℕ) :
    projection a d * drazinShellProj a d M m = 0 ∧
      drazinShellProj a d M m * projection a d = 0 := by
  unfold drazinShellProj
  constructor
  · calc
      projection a d *
          (complementaryProjection a d *
            shellProj (fittingNilpotentPart a d) M m *
            complementaryProjection a d)
          = (projection a d * complementaryProjection a d) *
              (shellProj (fittingNilpotentPart a d) M m *
                complementaryProjection a d) := by simp only [mul_assoc]
      _ = 0 := by
            simp only [projection_mul_complementaryProjection h, zero_mul]
  · calc
      (complementaryProjection a d *
          shellProj (fittingNilpotentPart a d) M m *
          complementaryProjection a d) * projection a d
          = (complementaryProjection a d *
              shellProj (fittingNilpotentPart a d) M m) *
              (complementaryProjection a d * projection a d) := by
                simp only [mul_assoc]
      _ = 0 := by
            simp only [complementaryProjection_mul_projection h, mul_zero]

theorem sum_drazinShellProj_eq_complementaryProjection (h : IsDrazinInverse a d k)
    {M : ℕ → R} (hM : PowerMPFamily (fittingNilpotentPart a d) M) :
    (∑ m ∈ Finset.range k, drazinShellProj a d M m) =
      complementaryProjection a d := by
  have h_sub : ∀ m, drazinShellProj a d M m =
      drazinRangeProj a d M m - drazinRangeProj a d M (m + 1) :=
    drazinShellProj_eq_sub a d M
  simp_rw [h_sub]
  rw [sum_range_sub_succ (drazinRangeProj a d M) k]
  have h0 : drazinRangeProj a d M 0 = complementaryProjection a d := by
    unfold drazinRangeProj
    rw [rangeProj_zero hM, mul_one, complementaryProjection_is_idempotent h]
  have hk : drazinRangeProj a d M k = 0 := by
    unfold drazinRangeProj rangeProj
    calc
      complementaryProjection a d *
          (fittingNilpotentPart a d ^ k * M k) * complementaryProjection a d
          = (complementaryProjection a d * fittingNilpotentPart a d ^ k) *
              M k * complementaryProjection a d := by simp only [mul_assoc]
      _ = 0 := by
            rw [complementaryProjection_mul_fittingNilpotentPart_pow_k h,
              zero_mul, zero_mul]
  rw [h0, hk, sub_zero]

theorem projection_add_sum_drazinShellProj (h : IsDrazinInverse a d k)
    {M : ℕ → R} (hM : PowerMPFamily (fittingNilpotentPart a d) M) :
    projection a d + (∑ m ∈ Finset.range k, drazinShellProj a d M m) = 1 := by
  rw [sum_drazinShellProj_eq_complementaryProjection h hM,
    projection_add_complementaryProjection]

theorem projection_add_sum_left_mul_shellProj (h : IsDrazinInverse a d k)
    (hk : 1 ≤ k) {M : ℕ → R}
    (hM : PowerMPFamily (fittingNilpotentPart a d) M) :
    projection a d +
        (∑ m ∈ Finset.range k, complementaryProjection a d *
          shellProj (fittingNilpotentPart a d) M m) = 1 ∧
      (∀ m, projection a d * (complementaryProjection a d *
        shellProj (fittingNilpotentPart a d) M m) = 0) := by
  have h_sum_Q :
      (∑ m ∈ Finset.range k, shellProj (fittingNilpotentPart a d) M m) = 1 := by
    unfold shellProj
    rw [sum_range_sub_succ (rangeProj (fittingNilpotentPart a d) M) k,
      rangeProj_zero hM]
    have hPk : rangeProj (fittingNilpotentPart a d) M k = 0 := by
      unfold rangeProj
      rw [fittingNilpotentPart_pow_k_eq_zero h hk, zero_mul]
    rw [hPk, sub_zero]
  refine ⟨?_, ?_⟩
  · rw [← Finset.mul_sum, h_sum_Q, mul_one, projection_add_complementaryProjection]
  · intro m
    rw [← mul_assoc, projection_mul_complementaryProjection h, zero_mul]

/-! ### Exact core-entry time on the full operator `a` -/

theorem drazinShellProj_mul_pow_succ_eq_zero (h : IsDrazinInverse a d k)
    {M : ℕ → R} (hM : PowerMPFamily (fittingNilpotentPart a d) M) (m : ℕ) :
    drazinShellProj a d M m * a ^ (m + 1) = 0 := by
  have hm1 : 1 ≤ m + 1 := Nat.succ_le_succ (Nat.zero_le m)
  have h1 : rangeProj (fittingNilpotentPart a d) M m *
      fittingNilpotentPart a d ^ (m + 1) = fittingNilpotentPart a d ^ (m + 1) := by
    calc
      rangeProj (fittingNilpotentPart a d) M m *
          fittingNilpotentPart a d ^ (m + 1)
          = rangeProj (fittingNilpotentPart a d) M m *
              (fittingNilpotentPart a d ^ (m + 1) * M (m + 1) *
                fittingNilpotentPart a d ^ (m + 1)) := by
              rw [(hM (m + 1)).aba_eq_a]
      _ = (rangeProj (fittingNilpotentPart a d) M m *
            rangeProj (fittingNilpotentPart a d) M (m + 1)) *
            fittingNilpotentPart a d ^ (m + 1) := by
              unfold rangeProj
              simp only [mul_assoc]
      _ = rangeProj (fittingNilpotentPart a d) M (m + 1) *
            fittingNilpotentPart a d ^ (m + 1) := by
              rw [rangeProj_mul_of_le hM (Nat.le_succ m)]
      _ = fittingNilpotentPart a d ^ (m + 1) := (hM (m + 1)).aba_eq_a
  have h2 : rangeProj (fittingNilpotentPart a d) M (m + 1) *
      fittingNilpotentPart a d ^ (m + 1) =
        fittingNilpotentPart a d ^ (m + 1) := (hM (m + 1)).aba_eq_a
  have hQ : shellProj (fittingNilpotentPart a d) M m *
      fittingNilpotentPart a d ^ (m + 1) = 0 := by
    unfold shellProj
    rw [sub_mul, h1, h2, sub_self]
  calc
    drazinShellProj a d M m * a ^ (m + 1)
        = complementaryProjection a d * shellProj (fittingNilpotentPart a d) M m *
            (complementaryProjection a d * a ^ (m + 1)) := by
              unfold drazinShellProj
              simp only [mul_assoc]
    _ = complementaryProjection a d *
          (shellProj (fittingNilpotentPart a d) M m *
            fittingNilpotentPart a d ^ (m + 1)) := by
              rw [complementaryProjection_mul_pow_eq_fittingNilpotentPart_pow h hm1,
                mul_assoc]
    _ = 0 := by rw [hQ, mul_zero]

/-- Recovery at degree `m`: right multiplication by the canonical recovery
factor recovers the dressed shell, and the displayed zero test is equivalent.
No nonzeroness or minimality of the Drazin index is asserted. -/
theorem drazinShellProj_not_absorbed_at_m (h : IsDrazinInverse a d k)
    {M : ℕ → R} (hM : PowerMPFamily (fittingNilpotentPart a d) M) (m : ℕ) (X : R) :
    (drazinShellProj a d M m * a ^ m) *
        (M m * complementaryProjection a d) = drazinShellProj a d M m ∧
      (X * drazinShellProj a d M m * a ^ m = 0 ↔
        X * drazinShellProj a d M m = 0) := by
  have h_mid : complementaryProjection a d * a ^ m =
      complementaryProjection a d *
        (complementaryProjection a d * fittingNilpotentPart a d ^ m) := by
    rw [← mul_assoc, complementaryProjection_is_idempotent h,
      complementaryProjection_mul_pow_eq h m]
  have h_rec :
      (drazinShellProj a d M m * a ^ m) *
          (M m * complementaryProjection a d) =
        drazinShellProj a d M m := by
    calc
      (drazinShellProj a d M m * a ^ m) * (M m * complementaryProjection a d)
          = complementaryProjection a d *
              shellProj (fittingNilpotentPart a d) M m *
              (complementaryProjection a d * a ^ m) * M m *
              complementaryProjection a d := by
                unfold drazinShellProj
                simp only [mul_assoc]
      _ = complementaryProjection a d *
              shellProj (fittingNilpotentPart a d) M m *
              (complementaryProjection a d *
                (complementaryProjection a d *
                  fittingNilpotentPart a d ^ m)) * M m *
              complementaryProjection a d := by rw [h_mid]
      _ = drazinShellProj a d M m * drazinRangeProj a d M m := by
            unfold drazinShellProj drazinRangeProj rangeProj
            simp only [mul_assoc]
      _ = drazinRangeProj a d M m * drazinRangeProj a d M m -
            drazinRangeProj a d M (m + 1) *
              drazinRangeProj a d M m := by
            rw [drazinShellProj_eq_sub, sub_mul]
      _ = drazinRangeProj a d M m - drazinRangeProj a d M (m + 1) := by
            rw [drazinRangeProj_mul_of_le h hM (le_refl m),
              drazinRangeProj_mul_of_ge h hM (Nat.le_succ m)]
      _ = drazinShellProj a d M m := (drazinShellProj_eq_sub a d M m).symm
  refine ⟨h_rec, ⟨?_, ?_⟩⟩
  · intro h_zero
    calc
      X * drazinShellProj a d M m
          = X * ((drazinShellProj a d M m * a ^ m) *
              (M m * complementaryProjection a d)) := by rw [h_rec]
      _ = (X * drazinShellProj a d M m * a ^ m) *
              (M m * complementaryProjection a d) := by
                simp only [mul_assoc]
      _ = 0 := by rw [h_zero, zero_mul]
  · intro h_zero
    rw [h_zero, zero_mul]

/-! ### Master resolution -/

/-- **`drazin_core_and_nilpotent_shells_partition_of_unity`.**
For any Drazin pair of index `k` and any Moore--Penrose family for the powers
of the nilpotent part:
1. `E_C + Σ_{m<k} S_m = 1`;
2. `E_C` and every `S_m` are idempotent;
3. `E_C` is two-sided orthogonal to every `S_m`;
4. distinct shells are mutually orthogonal;
5. `S_m = Q_m * E_N`;
6. `S_m * a^(m+1) = 0` and `X * S_m * a^m = 0 ↔ X * S_m = 0`. -/
theorem drazin_core_and_nilpotent_shells_partition_of_unity
    {a d : R} {k : ℕ} (h : IsDrazinInverse a d k) {M : ℕ → R}
    (hM : PowerMPFamily (fittingNilpotentPart a d) M) :
    (projection a d +
        (∑ m ∈ Finset.range k, drazinShellProj a d M m) = 1) ∧
      (projection a d * projection a d = projection a d) ∧
      (∀ m, drazinShellProj a d M m * drazinShellProj a d M m =
        drazinShellProj a d M m) ∧
      (∀ m, projection a d * drazinShellProj a d M m = 0 ∧
        drazinShellProj a d M m * projection a d = 0) ∧
      (∀ m r, m ≠ r →
        drazinShellProj a d M m * drazinShellProj a d M r = 0) ∧
      (∀ m, drazinShellProj a d M m =
        shellProj (fittingNilpotentPart a d) M m *
          complementaryProjection a d) ∧
      (∀ m, drazinShellProj a d M m * a ^ (m + 1) = 0) ∧
      (∀ m (X : R), X * drazinShellProj a d M m * a ^ m = 0 ↔
        X * drazinShellProj a d M m = 0) :=
  ⟨projection_add_sum_drazinShellProj h hM,
   projection_is_idempotent h,
   drazinShellProj_idem h hM,
   projection_drazinShellProj_orthogonal h M,
   fun _ _ hne => drazinShellProj_orthogonal h hM hne,
   drazinShellProj_eq_right_mul h hM,
   drazinShellProj_mul_pow_succ_eq_zero h hM,
   fun m X => (drazinShellProj_not_absorbed_at_m h hM m X).2⟩

/-! ### Regular-core invariance and the zero-th shell -/

theorem projection_pow_eq_projection (h : IsDrazinInverse a d k) {r : ℕ} (hr : 1 ≤ r) :
    projection a d ^ r = projection a d := by
  obtain ⟨s, rfl⟩ := Nat.exists_eq_add_of_le hr
  clear hr
  induction s with
  | zero => simp
  | succ s ih =>
      rw [Nat.add_succ, pow_succ, ih, projection_is_idempotent h]

/-- The regular core is time-invariant: `(E_C * a^r) * d^r = E_C` for every `r ≥ 1`. -/
theorem projection_mul_pow_mul_pow_eq_projection (h : IsDrazinInverse a d k) {r : ℕ}
    (hr : 1 ≤ r) :
    (projection a d * a ^ r) * d ^ r = projection a d := by
  have hcomm : Commute a d := h.comm
  have hpow : a ^ r * d ^ r = (a * d) ^ r := (hcomm.mul_pow r).symm
  calc
    (projection a d * a ^ r) * d ^ r
        = projection a d * (a ^ r * d ^ r) := by rw [mul_assoc]
    _ = projection a d * (a * d) ^ r := by rw [hpow]
    _ = projection a d * projection a d ^ r := rfl
    _ = projection a d := by
          rw [projection_pow_eq_projection h hr, projection_is_idempotent h]

/-- On positive powers, `N^m = a^m * E_N`. -/
theorem fittingNilpotentPart_pow_eq_pow_mul_complementaryProjection
    (h : IsDrazinInverse a d k) {m : ℕ} (hm : 1 ≤ m) :
    fittingNilpotentPart a d ^ m = a ^ m * complementaryProjection a d := by
  rw [← complementaryProjection_mul_fittingNilpotentPart_pow h hm,
    complementaryProjection_mul_fittingNilpotentPart_pow_eq h m]

/-- On positive powers, `N^m * E_N = N^m`. -/
theorem fittingNilpotentPart_pow_mul_complementaryProjection
    (h : IsDrazinInverse a d k) {m : ℕ} (hm : 1 ≤ m) :
    fittingNilpotentPart a d ^ m * complementaryProjection a d =
      fittingNilpotentPart a d ^ m := by
  rw [fittingNilpotentPart_pow_eq_pow_mul_complementaryProjection h hm, mul_assoc,
    complementaryProjection_is_idempotent h]

/-- The zero-th shell dies in one step: `S_0 * a = 0`. -/
theorem drazinShellProj_zero_mul_eq_zero (h : IsDrazinInverse a d k) {M : ℕ → R}
    (hM : PowerMPFamily (fittingNilpotentPart a d) M) :
    drazinShellProj a d M 0 * a = 0 := by
  simpa using drazinShellProj_mul_pow_succ_eq_zero h hM 0

end Drazin

end InfoGeometry.Canonical.DrazinNilpotentShell
