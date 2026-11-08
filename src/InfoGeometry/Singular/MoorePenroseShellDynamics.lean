/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import InfoGeometry.Singular.MoorePenrosePowerShells

/-!
# Power shells and action-sensitive extinction

Range shells have exact extinction for multiplication on the right by `a`.
Co-range shells have exact extinction for multiplication on the left by `a`.
The inverse at each power is independent data satisfying the existing
Moore--Penrose predicate. No reverse-order law is used.
-/

namespace InfoGeometry.Singular.MoorePenroseShellDynamics

open InfoGeometry.Singular.MoorePenrose
open InfoGeometry.Singular.MoorePenrosePowerShells

variable {R : Type*} [Ring R] [StarRing R]
variable (a : R) (g : ℕ → R)
variable (hg : ∀ m, IsMoorePenroseInverse (a ^ m) (g m))
include hg

/-- Reverse absorption follows by taking the star of forward absorption. -/
theorem rangeSupport_nested_reverse {i j : ℕ} (hij : i ≤ j) :
    (a ^ j * g j) * (a ^ i * g i) = a ^ j * g j := by
  have h := congrArg star (rangeSupport_nested a g hg hij)
  simpa only [star_mul, (hg i).ab_adj_eq, (hg j).ab_adj_eq] using h

theorem coRangeSupport_nested_reverse {i j : ℕ} (hij : i ≤ j) :
    (g i * a ^ i) * (g j * a ^ j) = g j * a ^ j := by
  have h := congrArg star (coRangeSupport_nested a g hg hij)
  simpa only [star_mul, (hg i).ba_adj_eq, (hg j).ba_adj_eq] using h

theorem rangeSupport_mul_max (i j : ℕ) :
    (a ^ i * g i) * (a ^ j * g j) = a ^ max i j * g (max i j) := by
  rcases le_total i j with hij | hji
  · rw [max_eq_right hij]
    exact rangeSupport_nested a g hg hij
  · rw [max_eq_left hji]
    exact rangeSupport_nested_reverse a g hg hji

theorem coRangeSupport_mul_max (i j : ℕ) :
    (g i * a ^ i) * (g j * a ^ j) = g (max i j) * a ^ max i j := by
  rcases le_total i j with hij | hji
  · rw [max_eq_right hij]
    exact coRangeSupport_nested_reverse a g hg hij
  · rw [max_eq_left hji]
    exact coRangeSupport_nested a g hg hji

theorem rangeSupport_mul_pow {i j : ℕ} (hij : i ≤ j) :
    (a ^ i * g i) * a ^ j = a ^ j := by
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hij
  calc
    (a ^ i * g i) * a ^ (i + t) = (a ^ i * g i * a ^ i) * a ^ t := by
      rw [pow_add, ← mul_assoc]
    _ = a ^ (i + t) := by rw [(hg i).aba_eq_a, ← pow_add]

theorem pow_mul_coRangeSupport {i j : ℕ} (hij : i ≤ j) :
    a ^ j * (g i * a ^ i) = a ^ j := by
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hij
  have hp : a ^ (i + t) = a ^ t * a ^ i := by rw [Nat.add_comm i t, pow_add]
  calc
    a ^ (i + t) * (g i * a ^ i) = a ^ t * (a ^ i * g i * a ^ i) := by
      rw [hp]
      simp only [mul_assoc]
    _ = a ^ (i + t) := by rw [(hg i).aba_eq_a, ← hp]

/-- Range shells are extinct after `m + 1` right actions. -/
theorem rangeShell_mul_pow_eq_zero {m r : ℕ} (hr : m + 1 ≤ r) :
    rangeShell a g m * a ^ r = 0 := by
  unfold rangeShell
  rw [sub_mul, rangeSupport_mul_pow a g hg (Nat.le_trans (Nat.le_succ m) hr),
    rangeSupport_mul_pow a g hg hr, sub_self]

/-- Co-range shells are extinct after `m + 1` left actions. -/
theorem pow_mul_deathShell_eq_zero {m r : ℕ} (hr : m + 1 ≤ r) :
    a ^ r * deathShell a g m = 0 := by
  unfold deathShell
  rw [mul_sub, pow_mul_coRangeSupport a g hg (Nat.le_trans (Nat.le_succ m) hr),
    pow_mul_coRangeSupport a g hg hr, sub_self]

/-- A left inverse on the shell proves survival through the previous step. -/
theorem rangeShell_recovery (m : ℕ) :
    (rangeShell a g m * a ^ m) * g m = rangeShell a g m := by
  rw [mul_assoc]
  unfold rangeShell
  rw [sub_mul, rangeSupport_nested a g hg (le_refl m),
    rangeSupport_nested_reverse a g hg (Nat.le_succ m)]

theorem deathShell_recovery (m : ℕ) :
    g m * (a ^ m * deathShell a g m) = deathShell a g m := by
  rw [← mul_assoc]
  unfold deathShell
  rw [mul_sub, coRangeSupport_nested a g hg (le_refl m),
    coRangeSupport_nested_reverse a g hg (Nat.le_succ m)]

theorem rangeShell_survives_iff (m : ℕ) (x : R) :
    x * rangeShell a g m * a ^ m = 0 ↔ x * rangeShell a g m = 0 := by
  constructor
  · intro hx
    calc
      x * rangeShell a g m = (x * rangeShell a g m * a ^ m) * g m := by
        rw [mul_assoc x _ (a ^ m), mul_assoc x _ (g m), rangeShell_recovery a g hg]
      _ = 0 := by rw [hx, zero_mul]
  · intro hx
    rw [hx, zero_mul]

theorem deathShell_survives_iff (m : ℕ) (x : R) :
    a ^ m * (deathShell a g m * x) = 0 ↔ deathShell a g m * x = 0 := by
  constructor
  · intro hx
    calc
      deathShell a g m * x = g m * (a ^ m * (deathShell a g m * x)) := by
        rw [← mul_assoc (a ^ m) _ x, ← mul_assoc (g m) _ x,
          deathShell_recovery a g hg]
      _ = 0 := by rw [hx, mul_zero]
  · intro hx
    rw [hx, mul_zero]

theorem rangeShell_orthogonal_of_ne {i j : ℕ} (hij : i ≠ j) :
    rangeShell a g i * rangeShell a g j = 0 := by
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · exact rangeShell_orthogonal a g hg hlt
  · have h := congrArg star (rangeShell_orthogonal a g hg hgt)
    simpa only [star_mul, star_zero,
      (rangeShell_isStarProjection a g hg i).isSelfAdjoint.star_eq,
      (rangeShell_isStarProjection a g hg j).isSelfAdjoint.star_eq] using h

theorem deathShell_orthogonal_of_ne {i j : ℕ} (hij : i ≠ j) :
    deathShell a g i * deathShell a g j = 0 := by
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · have h := congrArg star (deathShell_orthogonal a g hg hlt)
    simpa only [star_mul, star_zero,
      (deathShell_isStarProjection a g hg i).isSelfAdjoint.star_eq,
      (deathShell_isStarProjection a g hg j).isSelfAdjoint.star_eq] using h
  · exact deathShell_orthogonal a g hg hgt

omit hg in
/-- An abstract extinction criterion, with a nonzero state required explicitly. -/
theorem right_extinction_iff {s b x : R} {m : ℕ}
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

theorem rangeShell_exact_extinction {m : ℕ} {x : R}
    (hx : x * rangeShell a g m ≠ 0) (r : ℕ) :
    x * rangeShell a g m * a ^ r = 0 ↔ m < r :=
  right_extinction_iff a (rangeShell_mul_pow_eq_zero a g hg (le_refl (m + 1)))
    (rangeShell_recovery a g hg m) hx r

end InfoGeometry.Singular.MoorePenroseShellDynamics
