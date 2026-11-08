/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Singular.NilpotentShellFiltration

/-!
# Right-action range shells and left-action co-range shells

Range shells give exact death time for rows/covectors. The transposed family
gives the dual shells for column action. Each power has its own MP inverse;
no reverse-order rule for pseudoinverses is assumed. Nilpotence is needed for
the finite partition, not for the nesting or absorption identities.
-/

namespace InfoGeometry.Singular.NilpotentShellFiltration
open Matrix BigOperators
variable {n : Type*} [Fintype n] [DecidableEq n]
variable {N : Matrix n n ℝ} {M : ℕ → Matrix n n ℝ}
variable (hM : PowerMPFamily N M)
include hM

theorem rangeProj_mul_pow {a b : ℕ} (hab : a ≤ b) :
    rangeProj N M a * N ^ b = N ^ b := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hab
  calc
    _ = (N ^ a * M a * N ^ a) * N ^ d := by
      simp only [rangeProj, pow_add, mul_assoc]
    _ = _ := by rw [(hM a).aba_eq_a, pow_add]

/-- The range shell kills every sufficiently high power on its right. -/
theorem shellProj_mul_pow_eq_zero {m r : ℕ} (hr : m + 1 ≤ r) :
    shellProj N M m * N ^ r = 0 := by
  rw [shellProj, sub_mul, rangeProj_mul_pow hM (le_trans (Nat.le_succ m) hr),
    rangeProj_mul_pow hM hr, sub_self]

theorem shellProj_recover (m : ℕ) :
    (shellProj N M m * N ^ m) * M m = shellProj N M m := by
  rw [mul_assoc]
  change (rangeProj N M m - rangeProj N M (m + 1)) * rangeProj N M m = _
  rw [sub_mul, rangeProj_mul_of_le hM (le_refl m),
    rangeProj_mul_of_ge hM (Nat.le_succ m)]
  rfl

/-- A nonzero right-action shell state cannot die before its designated step. -/
theorem shellProj_right_absorption_iff (X : Matrix n n ℝ) (m : ℕ) :
    X * shellProj N M m * N ^ m = 0 ↔ X * shellProj N M m = 0 := by
  constructor
  · intro hx
    have h := congrArg (fun Y => Y * M m) hx
    simpa only [mul_assoc, ← mul_assoc (shellProj N M m), shellProj_recover hM,
      zero_mul] using h
  · intro hx
    rw [hx, zero_mul]

/-- Transposition reverses the four Penrose equations and preserves their scope. -/
theorem transpose_power_family : PowerMPFamily N.transpose (fun m => (M m).transpose) := by
  have hstar (X : Matrix n n ℝ) : star X = X.transpose := by
    ext i j
    simp [Matrix.star_apply, Matrix.transpose_apply]
  intro m
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [Matrix.transpose_mul, Matrix.transpose_pow, mul_assoc] using
      congrArg Matrix.transpose (hM m).aba_eq_a
  · simpa only [Matrix.transpose_mul, Matrix.transpose_pow, mul_assoc] using
      congrArg Matrix.transpose (hM m).bab_eq_b
  · change ((N.transpose ^ m) * (M m).transpose).transpose =
      (N.transpose ^ m) * (M m).transpose
    have h := congrArg Matrix.transpose (hM m).ba_adj_eq
    rw [hstar] at h
    simpa only [Matrix.transpose_mul, Matrix.transpose_pow, Matrix.transpose_transpose] using h
  · change ((M m).transpose * N.transpose ^ m).transpose =
      (M m).transpose * N.transpose ^ m
    have h := congrArg Matrix.transpose (hM m).ab_adj_eq
    rw [hstar] at h
    simpa only [Matrix.transpose_mul, Matrix.transpose_pow, Matrix.transpose_transpose] using h

omit hM in
def corangeShell (N : Matrix n n ℝ) (M : ℕ → Matrix n n ℝ) (m : ℕ) :=
  M m * N ^ m - M (m + 1) * N ^ (m + 1)

theorem corangeShell_eq_transpose_range (m : ℕ) :
    corangeShell N M m = shellProj N.transpose (fun j => (M j).transpose) m := by
  have hstar (X : Matrix n n ℝ) : star X = X.transpose := by
    ext i j
    simp [Matrix.star_apply, Matrix.transpose_apply]
  have ht (j : ℕ) : M j * N ^ j = N.transpose ^ j * (M j).transpose := by
    have h := (hM j).ba_adj_eq.symm
    rw [hstar] at h
    simpa only [Matrix.transpose_mul, Matrix.transpose_pow] using h
  simp only [corangeShell, shellProj, rangeProj, ht]

theorem corangeShell_symm (m : ℕ) : (corangeShell N M m).transpose = corangeShell N M m := by
  rw [corangeShell_eq_transpose_range hM]
  exact shellProj_symm (transpose_power_family hM) m

theorem corangeShell_idem (m : ℕ) : corangeShell N M m * corangeShell N M m = corangeShell N M m := by
  rw [corangeShell_eq_transpose_range hM]
  exact shellProj_idem (transpose_power_family hM) m

theorem corangeShell_orthogonal {a b : ℕ} (hab : a ≠ b) :
    corangeShell N M a * corangeShell N M b = 0 := by
  simp only [corangeShell_eq_transpose_range hM]
  exact shellProj_orthogonal (transpose_power_family hM) hab

theorem corangeShell_partition {k : ℕ} (hk : N ^ k = 0) :
    (∑ m ∈ Finset.range k, corangeShell N M m) = 1 := by
  simp only [corangeShell_eq_transpose_range hM]
  apply shellProj_partition_of_unity (transpose_power_family hM)
  simpa only [Matrix.transpose_pow, Matrix.transpose_zero] using congrArg Matrix.transpose hk

theorem pow_mul_corangeShell_eq_zero {m r : ℕ} (hr : m + 1 ≤ r) :
    N ^ r * corangeShell N M m = 0 := by
  have h := shellProj_mul_pow_eq_zero (transpose_power_family hM) hr
  rw [← corangeShell_eq_transpose_range hM] at h
  simpa only [Matrix.transpose_mul, ← Matrix.transpose_pow, Matrix.transpose_transpose,
    corangeShell_symm hM, Matrix.transpose_zero] using congrArg Matrix.transpose h

theorem corangeShell_recover (m : ℕ) :
    M m * (N ^ m * corangeShell N M m) = corangeShell N M m := by
  have h := shellProj_recover (transpose_power_family hM) m
  rw [← corangeShell_eq_transpose_range hM] at h
  simpa only [Matrix.transpose_mul, ← Matrix.transpose_pow, Matrix.transpose_transpose,
    corangeShell_symm hM] using congrArg Matrix.transpose h

theorem corangeShell_left_absorption_iff (X : Matrix n n ℝ) (m : ℕ) :
    N ^ m * (corangeShell N M m * X) = 0 ↔ corangeShell N M m * X = 0 := by
  constructor
  · intro hx
    have h := congrArg (fun Y => M m * Y) hx
    simpa only [← mul_assoc, corangeShell_recover hM, mul_zero] using h
  · intro hx
    rw [hx, mul_zero]

end InfoGeometry.Singular.NilpotentShellFiltration
