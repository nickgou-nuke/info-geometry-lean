/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.DrazinNilpotentShellResolution

/-!
# Candidate: exact right extinction and leading shell steps

UNVERIFIED scratch candidate; no compilation was run during the shared QA lane.
Adapted from upstream/feat/drazin-shell-cascade and
upstream/feat/peirce-square-zero-mp, using only native shell definitions.

The abstract extinction lemma requires only a ring. The shell applications
require an arbitrary star ring and the native canonical `PowerMPFamily`.
All evolution is right multiplication by `a`. No shell nonzeroness, minimal
Drazin index, self-adjoint complement, or finite-dimensional carrier is assumed.
The nonzero state hypothesis in exact extinction is explicit.

Suggested destinations: the abstract criterion in a small algebra owner;
the shell consequences beside the native shell-resolution/cascade API.
Suggested audit heads are listed at the end, as comments only.
-/

namespace InfoGeometry.Canonical.DrazinShellExtinctionCandidate

open InfoGeometry.Canonical.Drazin
open InfoGeometry.Canonical.Drazin.IsDrazinInverse
open InfoGeometry.Canonical.DrazinNilpotentShell
open scoped BigOperators

section Ring
variable {R : Type*} [Ring R]

/-- Recovery at step `m` and extinction at step `m+1` determine the exact
right extinction time of every nonzero supported state. -/
theorem right_extinction_iff (a : R) {s b x : R} {m : ℕ}
    (hkill : s * a ^ (m + 1) = 0) (hrec : (s * a ^ m) * b = s)
    (hx : x * s ≠ 0) (r : ℕ) : x * s * a ^ r = 0 ↔ m < r := by
  constructor
  · intro hr
    by_contra hnot
    have hrm : r ≤ m := Nat.le_of_not_gt hnot
    obtain ⟨t, ht⟩ := Nat.exists_eq_add_of_le hrm
    have hm : x * s * a ^ m = 0 := by
      rw [ht, pow_add, ← mul_assoc, hr, zero_mul]
    apply hx
    calc
      x * s = (x * s * a ^ m) * b := by
        rw [mul_assoc x s (a ^ m), mul_assoc x (s * a ^ m) b, hrec]
      _ = 0 := by rw [hm, zero_mul]
  · intro hr
    obtain ⟨t, ht⟩ := Nat.exists_eq_add_of_le (Nat.succ_le_of_lt hr)
    rw [ht, pow_add, ← mul_assoc, mul_assoc x s (a ^ (m + 1)),
      hkill, mul_zero, zero_mul]

end Ring

section Shells
variable {R : Type*} [Ring R] [StarRing R]
variable {a d : R} {k : ℕ} {M : ℕ → R}

local notation "F" => complementaryProjection a d
local notation "S" => drazinShellProj a d M
local notation "H" => drazinRangeProj a d M

theorem drazinShellProj_exact_extinction (hD : IsDrazinInverse a d k)
    (hM : PowerMPFamily (fittingNilpotentPart a d) M)
    {m : ℕ} {x : R} (hx : x * S m ≠ 0) (r : ℕ) :
    x * S m * a ^ r = 0 ↔ m < r :=
  right_extinction_iff a (drazinShellProj_mul_pow_succ_eq_zero hD hM m)
    (drazinShellProj_not_absorbed_at_m hD hM m x).1 hx r

/-- Finite partial sums retain the remaining dressed range support. -/
theorem drazinShellProj_partial_sum (hD : IsDrazinInverse a d k)
    (hM : PowerMPFamily (fittingNilpotentPart a d) M) (m : ℕ) :
    (∑ r ∈ Finset.range m, S r) = F - H m := by
  simp_rw [drazinShellProj_eq_sub]
  rw [sum_range_sub_succ]
  have hzero : H 0 = F := by
    unfold drazinRangeProj
    rw [rangeProj_zero hM, mul_one, complementaryProjection_is_idempotent hD]
  rw [hzero]

/-- A right-supported element meets a dressed range by power and recovery. -/
theorem supported_mul_drazinRangeProj (hD : IsDrazinInverse a d k)
    {x : R} (hx : x * F = x) (m : ℕ) :
    x * H m = (x * a ^ m) * (M m * F) := by
  calc
    x * H m = (x * (F * fittingNilpotentPart a d ^ m)) * (M m * F) := by
      simp only [drazinRangeProj, rangeProj, mul_assoc]
    _ = (x * (F * a ^ m)) * (M m * F) := by
      rw [← complementaryProjection_mul_pow_eq hD]
    _ = (x * a ^ m) * (M m * F) := by
      rw [← mul_assoc x F (a ^ m), hx]

theorem drazinShellProj_right_complement (hD : IsDrazinInverse a d k) (m : ℕ) :
    S m * F = S m := by
  unfold drazinShellProj
  simp only [mul_assoc, complementaryProjection_is_idempotent hD]

theorem drazinShellProj_step_right_complement (hD : IsDrazinInverse a d k) (m : ℕ) :
    (S m * a) * F = S m * a := by
  rw [mul_assoc, ← complementaryProjection_comm_self hD, ← mul_assoc,
    drazinShellProj_right_complement hD]

theorem drazinShellProj_step_range_zero (hD : IsDrazinInverse a d k)
    (hM : PowerMPFamily (fittingNilpotentPart a d) M) (m : ℕ) :
    (S m * a) * H m = 0 := by
  rw [supported_mul_drazinRangeProj hD (drazinShellProj_step_right_complement hD m),
    mul_assoc (S m) a (a ^ m), ← pow_succ',
    drazinShellProj_mul_pow_succ_eq_zero hD hM, zero_mul]

/-- A right step lands in the sum of strictly lower shells. -/
theorem drazinShellProj_step_eq_lower (hD : IsDrazinInverse a d k)
    (hM : PowerMPFamily (fittingNilpotentPart a d) M) (m : ℕ) :
    S m * a = (S m * a) * (∑ r ∈ Finset.range m, S r) := by
  rw [drazinShellProj_partial_sum hD hM, mul_sub,
    drazinShellProj_step_right_complement hD,
    drazinShellProj_step_range_zero hD hM, sub_zero]

theorem drazinShellProj_mul_pow_eq_zero (hD : IsDrazinInverse a d k)
    (hM : PowerMPFamily (fittingNilpotentPart a d) M)
    {m r : ℕ} (hr : m + 1 ≤ r) : S m * a ^ r = 0 := by
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hr
  rw [pow_add, ← mul_assoc, drazinShellProj_mul_pow_succ_eq_zero hD hM, zero_mul]

theorem lower_shell_sum_mul_pow_eq_zero (hD : IsDrazinInverse a d k)
    (hM : PowerMPFamily (fittingNilpotentPart a d) M) (m : ℕ) :
    (∑ r ∈ Finset.range m, S r) * a ^ m = 0 := by
  rw [Finset.sum_mul]
  apply Finset.sum_eq_zero
  intro r hr
  exact drazinShellProj_mul_pow_eq_zero hD hM
    (Nat.succ_le_of_lt (Finset.mem_range.mp hr))

/-- After the next `m` steps only the adjacent lower block contributes. -/
theorem drazinShellProj_leading_step_power (hD : IsDrazinInverse a d k)
    (hM : PowerMPFamily (fittingNilpotentPart a d) M) (m : ℕ) :
    (S (m + 1) * a) * a ^ m = ((S (m + 1) * a) * S m) * a ^ m := by
  calc
    (S (m + 1) * a) * a ^ m =
        ((S (m + 1) * a) * (∑ r ∈ Finset.range (m + 1), S r)) * a ^ m := by
      rw [← drazinShellProj_step_eq_lower hD hM (m + 1)]
    _ = ((S (m + 1) * a) * S m) * a ^ m := by
      rw [Finset.sum_range_succ, mul_add, add_mul,
        mul_assoc (S (m + 1) * a) (∑ r ∈ Finset.range m, S r) (a ^ m),
        lower_shell_sum_mul_pow_eq_zero hD hM, mul_zero, zero_add]

/-- The adjacent lower block detects every right-action shell state.
This is a zero-test equivalence, not an assertion that any shell is nonzero. -/
theorem drazinShellProj_leading_step_faithful (hD : IsDrazinInverse a d k)
    (hM : PowerMPFamily (fittingNilpotentPart a d) M) (m : ℕ) (x : R) :
    x * S (m + 1) * a * S m = 0 ↔ x * S (m + 1) = 0 := by
  constructor
  · intro hx
    apply (drazinShellProj_not_absorbed_at_m hD hM (m + 1) x).2.mp
    calc
      x * S (m + 1) * a ^ (m + 1) = x * ((S (m + 1) * a) * a ^ m) := by
        rw [pow_succ']
        simp only [mul_assoc]
      _ = x * (((S (m + 1) * a) * S m) * a ^ m) := by
        rw [drazinShellProj_leading_step_power hD hM]
      _ = (x * S (m + 1) * a * S m) * a ^ m := by simp only [mul_assoc]
      _ = 0 := by rw [hx, zero_mul]
  · intro hx
    rw [hx, zero_mul, zero_mul]

end Shells
end InfoGeometry.Canonical.DrazinShellExtinctionCandidate

/- Suggested audit heads after a parent-controlled locked check:
#print axioms InfoGeometry.Canonical.DrazinShellExtinctionCandidate.right_extinction_iff
#print axioms InfoGeometry.Canonical.DrazinShellExtinctionCandidate.drazinShellProj_exact_extinction
#print axioms InfoGeometry.Canonical.DrazinShellExtinctionCandidate.drazinShellProj_step_eq_lower
#print axioms InfoGeometry.Canonical.DrazinShellExtinctionCandidate.drazinShellProj_leading_step_power
#print axioms InfoGeometry.Canonical.DrazinShellExtinctionCandidate.drazinShellProj_leading_step_faithful
-/
