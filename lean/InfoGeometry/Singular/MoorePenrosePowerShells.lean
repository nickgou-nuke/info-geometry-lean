/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Singular.MoorePenroseSectors

/-!
# Power-support shells

MP inverses are taken for each actual power, not by powering a single MP
inverse. Range shells and kernel-growth (death) shells are different
filtrations. Their telescoping sum is the ambient identity for a nilpotent
operator. Restriction to a Drazin summand is a separate carrier choice.
-/

namespace InfoGeometry.Singular.MoorePenrosePowerShells

open InfoGeometry.Singular.MoorePenrose
open InfoGeometry.Singular.MoorePenroseSectors
open scoped BigOperators

variable {R : Type*} [Ring R] [StarRing R] (a : R) (g : ℕ → R)

/-- Successive differences of range support projectors. -/
def rangeShell (n : ℕ) : R := a ^ n * g n - a ^ (n + 1) * g (n + 1)

/-- Successive kernel growth, expressed with co-range projectors. -/
def deathShell (n : ℕ) : R := g n * a ^ n - g (n + 1) * a ^ (n + 1)

variable (hg : ∀ n, IsMoorePenroseInverse (a ^ n) (g n))

theorem rangeSupport_nested {i j : ℕ} (hij : i ≤ j) :
    (a ^ i * g i) * (a ^ j * g j) = a ^ j * g j := by
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hij
  calc
    (a ^ i * g i) * (a ^ (i + t) * g (i + t)) =
        (a ^ i * g i * a ^ i) * a ^ t * g (i + t) := by
          rw [pow_add]; simp only [mul_assoc]
    _ = a ^ (i + t) * g (i + t) := by rw [(hg i).aba_eq_a, ← pow_add]

theorem coRangeSupport_nested {i j : ℕ} (hij : i ≤ j) :
    (g j * a ^ j) * (g i * a ^ i) = g j * a ^ j := by
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hij
  calc
    (g (i + t) * a ^ (i + t)) * (g i * a ^ i) =
        g (i + t) * a ^ t * (a ^ i * g i * a ^ i) := by
          rw [show i + t = t + i from Nat.add_comm i t, pow_add]
          simp only [mul_assoc]
    _ = g (i + t) * a ^ (i + t) := by
      rw [(hg i).aba_eq_a, mul_assoc, ← pow_add, Nat.add_comm t i]

theorem rangeShell_isStarProjection (n : ℕ) : IsStarProjection (rangeShell a g n) :=
  (support_isStarProjection (hg (n + 1))).1.sub_of_mul_eq_right
    (support_isStarProjection (hg n)).1 (rangeSupport_nested a g hg (Nat.le_succ n))

theorem deathShell_isStarProjection (n : ℕ) : IsStarProjection (deathShell a g n) :=
  (support_isStarProjection (hg (n + 1))).2.sub_of_mul_eq_left
    (support_isStarProjection (hg n)).2 (coRangeSupport_nested a g hg (Nat.le_succ n))

/-- Range shells with distinct ordered levels multiply to zero. -/
theorem rangeShell_orthogonal {i j : ℕ} (hij : i < j) :
    rangeShell a g i * rangeShell a g j = 0 := by
  unfold rangeShell
  rw [sub_mul, mul_sub, mul_sub,
    rangeSupport_nested a g hg (Nat.le_of_lt hij),
    rangeSupport_nested a g hg (by omega : i ≤ j + 1),
    rangeSupport_nested a g hg (by omega : i + 1 ≤ j),
    rangeSupport_nested a g hg (by omega : i + 1 ≤ j + 1), sub_self]

theorem deathShell_orthogonal {i j : ℕ} (hij : i < j) :
    deathShell a g j * deathShell a g i = 0 := by
  unfold deathShell
  rw [sub_mul, mul_sub, mul_sub,
    coRangeSupport_nested a g hg (Nat.le_of_lt hij),
    coRangeSupport_nested a g hg (by omega : i + 1 ≤ j),
    coRangeSupport_nested a g hg (by omega : i ≤ j + 1),
    coRangeSupport_nested a g hg (by omega : i + 1 ≤ j + 1)]
  abel

/-- The kernel-difference interpretation is distinct from range differences. -/
theorem deathShell_eq_kernel_difference (n : ℕ) :
    deathShell a g n = (1 - g (n + 1) * a ^ (n + 1)) - (1 - g n * a ^ n) := by
  unfold deathShell
  abel

lemma telescope (f : ℕ → R) (k : ℕ) :
    (∑ i ∈ Finset.range k, (f i - f (i + 1))) = f 0 - f k := by
  induction k with
  | zero => simp
  | succ k ih => rw [Finset.sum_range_succ, ih]; abel

/-- The range-shell sum on the ambient nilpotent carrier is one. -/
theorem rangeShell_sum {k : ℕ} (hk : a ^ k = 0) :
    (∑ i ∈ Finset.range k, rangeShell a g i) = 1 := by
  have hzero : g 0 = 1 := by simpa using (hg 0).aba_eq_a
  rw [rangeShell, telescope]
  simp [hzero, hk]

/-- Kernel-growth shells also sum to one, but need not equal range shells. -/
theorem deathShell_sum {k : ℕ} (hk : a ^ k = 0) :
    (∑ i ∈ Finset.range k, deathShell a g i) = 1 := by
  have hzero : g 0 = 1 := by simpa using (hg 0).aba_eq_a
  rw [deathShell, telescope]
  simp [hzero, hk]

end InfoGeometry.Singular.MoorePenrosePowerShells
