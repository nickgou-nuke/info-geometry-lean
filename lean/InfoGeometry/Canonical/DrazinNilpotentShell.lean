/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib.Tactic
import InfoGeometry.Canonical.MoorePenrose

/-!
# Nilpotent shell filtration in an arbitrary star ring

This is the ring-generic owner for the range and shell projectors of a
nilpotent endomorphism.  The matrix development in
`InfoGeometry.Singular.NilpotentShellFiltration` is the `Matrix n n ℝ` instance;
nothing below assumes commutativity, diagonalizability, or finite dimension.

For `N : R` with a Moore--Penrose inverse `M m` for every power `N ^ m`, the
`m`-th range projector is `P m = N ^ m * M m` and the `m`-th shell projector is
`Q m = P m - P (m + 1)`.  The shells are idempotent, mutually orthogonal, and
(under nilpotence) sum to the identity.
-/

namespace InfoGeometry.Canonical.DrazinNilpotentShell

open InfoGeometry.Canonical.Drazin
open InfoGeometry.Canonical.MoorePenrose

variable {R : Type*} [Ring R] [StarRing R]

/-- A Moore--Penrose choice for every power of an endomorphism. -/
def PowerMPFamily (N : R) (M : ℕ → R) : Prop :=
  ∀ m, IsMoorePenroseInverse (N ^ m) (M m)

/-- Orthogonal range support of the `m`-th power. -/
def rangeProj (N : R) (M : ℕ → R) (m : ℕ) : R :=
  N ^ m * M m

/-- Difference of consecutive range supports. -/
def shellProj (N : R) (M : ℕ → R) (m : ℕ) : R :=
  rangeProj N M m - rangeProj N M (m + 1)

variable {N : R} {M : ℕ → R}

theorem rangeProj_symm (hM : PowerMPFamily N M) (m : ℕ) :
    star (rangeProj N M m) = rangeProj N M m :=
  (hM m).ab_star

theorem rangeProj_zero (hM : PowerMPFamily N M) : rangeProj N M 0 = 1 := by
  simpa [rangeProj, pow_zero] using (hM 0).aba_eq_a

theorem rangeProj_mul_of_le (hM : PowerMPFamily N M) {a b : ℕ} (hab : a ≤ b) :
    rangeProj N M a * rangeProj N M b = rangeProj N M b := by
  have hpow : N ^ b = N ^ a * N ^ (b - a) := by
    rw [← pow_add, Nat.add_sub_of_le hab]
  unfold rangeProj
  calc
    (N ^ a * M a) * (N ^ b * M b)
        = (N ^ a * M a) * ((N ^ a * N ^ (b - a)) * M b) := by rw [hpow]
    _ = (N ^ a * M a * N ^ a) * (N ^ (b - a) * M b) := by
          simp only [mul_assoc]
    _ = N ^ a * (N ^ (b - a) * M b) := by rw [(hM a).aba_eq_a]
    _ = (N ^ a * N ^ (b - a)) * M b := by rw [mul_assoc]
    _ = N ^ b * M b := by rw [← hpow]

theorem rangeProj_mul_of_ge (hM : PowerMPFamily N M) {a b : ℕ} (hab : a ≤ b) :
    rangeProj N M b * rangeProj N M a = rangeProj N M b := by
  calc
    rangeProj N M b * rangeProj N M a
        = star (rangeProj N M b) * star (rangeProj N M a) := by
            rw [rangeProj_symm hM b, rangeProj_symm hM a]
    _ = star (rangeProj N M a * rangeProj N M b) := (star_mul _ _).symm
    _ = star (rangeProj N M b) := by rw [rangeProj_mul_of_le hM hab]
    _ = rangeProj N M b := rangeProj_symm hM b

theorem rangeProj_mul (hM : PowerMPFamily N M) (a b : ℕ) :
    rangeProj N M a * rangeProj N M b = rangeProj N M (max a b) := by
  rcases le_total a b with hab | hba
  · rw [max_eq_right hab, rangeProj_mul_of_le hM hab]
  · rw [max_eq_left hba, rangeProj_mul_of_ge hM hba]

theorem shellProj_symm (hM : PowerMPFamily N M) (m : ℕ) :
    star (shellProj N M m) = shellProj N M m := by
  unfold shellProj
  rw [star_sub, rangeProj_symm hM m, rangeProj_symm hM (m + 1)]

theorem shellProj_idem (hM : PowerMPFamily N M) (m : ℕ) :
    shellProj N M m * shellProj N M m = shellProj N M m := by
  unfold shellProj
  rw [sub_mul, mul_sub, mul_sub,
    rangeProj_mul_of_le hM (le_refl m),
    rangeProj_mul_of_le hM (Nat.le_succ m),
    rangeProj_mul_of_ge hM (Nat.le_succ m),
    rangeProj_mul_of_le hM (le_refl (m + 1))]
  abel

theorem shellProj_mul_of_lt (hM : PowerMPFamily N M) {m r : ℕ} (hmr : m < r) :
    shellProj N M m * shellProj N M r = 0 := by
  unfold shellProj
  rw [sub_mul, mul_sub, mul_sub,
    rangeProj_mul_of_le hM (le_of_lt hmr),
    rangeProj_mul_of_le hM (le_of_lt (Nat.lt_succ_of_lt hmr)),
    rangeProj_mul_of_le hM (Nat.succ_le_of_lt hmr),
    rangeProj_mul_of_le hM (le_trans (Nat.succ_le_of_lt hmr) (Nat.le_succ r))]
  abel

theorem shellProj_orthogonal (hM : PowerMPFamily N M) {m r : ℕ} (hne : m ≠ r) :
    shellProj N M m * shellProj N M r = 0 := by
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact shellProj_mul_of_lt hM hlt
  · calc
      shellProj N M m * shellProj N M r
          = star (shellProj N M m) * star (shellProj N M r) := by
              rw [shellProj_symm hM m, shellProj_symm hM r]
      _ = star (shellProj N M r * shellProj N M m) := (star_mul _ _).symm
      _ = star (0 : R) := by rw [shellProj_mul_of_lt hM hgt]
      _ = 0 := star_zero _

theorem rangeProj_mul_pow (hM : PowerMPFamily N M) {a b : ℕ} (hab : a ≤ b) :
    rangeProj N M a * N ^ b = N ^ b := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hab
  calc
    rangeProj N M a * N ^ (a + d)
        = (N ^ a * M a * N ^ a) * N ^ d := by
            simp only [rangeProj, pow_add, mul_assoc]
    _ = N ^ a * N ^ d := by rw [(hM a).aba_eq_a]
    _ = N ^ (a + d) := by rw [pow_add]

theorem shellProj_mul_pow_eq_zero (hM : PowerMPFamily N M) {m r : ℕ}
    (hr : m + 1 ≤ r) :
    shellProj N M m * N ^ r = 0 := by
  rw [shellProj, sub_mul,
    rangeProj_mul_pow hM (le_trans (Nat.le_succ m) hr),
    rangeProj_mul_pow hM hr, sub_self]

theorem shellProj_recover (hM : PowerMPFamily N M) (m : ℕ) :
    (shellProj N M m * N ^ m) * M m = shellProj N M m := by
  rw [mul_assoc]
  change (rangeProj N M m - rangeProj N M (m + 1)) * rangeProj N M m = _
  rw [sub_mul, rangeProj_mul_of_le hM (le_refl m),
    rangeProj_mul_of_ge hM (Nat.le_succ m)]
  rfl

theorem shellProj_right_absorption_iff (hM : PowerMPFamily N M) (X : R) (m : ℕ) :
    X * shellProj N M m * N ^ m = 0 ↔ X * shellProj N M m = 0 := by
  constructor
  · intro hx
    have h := congrArg (fun Y => Y * M m) hx
    rw [zero_mul] at h
    have h' : X * ((shellProj N M m * N ^ m) * M m) = 0 := by
      simpa only [mul_assoc] using h
    rwa [shellProj_recover hM] at h'
  · intro hx
    rw [hx, zero_mul]

lemma sum_range_sub_succ {G : Type*} [AddCommGroup G] (f : ℕ → G) :
    ∀ k : ℕ, (∑ m ∈ Finset.range k, (f m - f (m + 1))) = f 0 - f k
  | 0 => by simp
  | k + 1 => by
      rw [Finset.sum_range_succ, sum_range_sub_succ f k]
      abel

theorem shellProj_partition_of_unity (hM : PowerMPFamily N M) {k : ℕ}
    (hNk : N ^ k = 0) :
    (∑ m ∈ Finset.range k, shellProj N M m) = 1 := by
  unfold shellProj
  rw [sum_range_sub_succ (rangeProj N M), rangeProj_zero hM]
  have hk : rangeProj N M k = 0 := by
    unfold rangeProj
    rw [hNk, zero_mul]
  rw [hk, sub_zero]

theorem nilpotent_shell_projectors_orthogonal_partition (hM : PowerMPFamily N M)
    {k : ℕ} (hNk : N ^ k = 0) :
    (∀ m, star (shellProj N M m) = shellProj N M m) ∧
    (∀ m, shellProj N M m * shellProj N M m = shellProj N M m) ∧
    (∀ m r, m ≠ r → shellProj N M m * shellProj N M r = 0) ∧
    ((∑ m ∈ Finset.range k, shellProj N M m) = 1) :=
  ⟨shellProj_symm hM, shellProj_idem hM,
    fun _ _ hne => shellProj_orthogonal hM hne,
    shellProj_partition_of_unity hM hNk⟩

end InfoGeometry.Canonical.DrazinNilpotentShell
