/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Singular.MoorePenrose

open Matrix BigOperators

namespace InfoGeometry.Singular.NilpotentShellFiltration

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- A Moore--Penrose choice for every power of an endomorphism. -/
def PowerMPFamily (N : Matrix n n ℝ) (M : ℕ → Matrix n n ℝ) : Prop :=
  ∀ m, MoorePenrose.IsMoorePenroseInverse (N ^ m) (M m)

/-- Orthogonal range support of the `m`-th power. -/
def rangeProj (N : Matrix n n ℝ) (M : ℕ → Matrix n n ℝ) (m : ℕ) : Matrix n n ℝ :=
  N ^ m * M m

/-- Difference of consecutive range supports. -/
def shellProj (N : Matrix n n ℝ) (M : ℕ → Matrix n n ℝ) (m : ℕ) : Matrix n n ℝ :=
  rangeProj N M m - rangeProj N M (m + 1)

theorem rangeProj_symm {N : Matrix n n ℝ} {M : ℕ → Matrix n n ℝ}
    (hM : PowerMPFamily N M) (m : ℕ) :
    (rangeProj N M m)ᵀ = rangeProj N M m :=
  (hM m).ab_adj_eq

theorem rangeProj_mul_of_le {N : Matrix n n ℝ} {M : ℕ → Matrix n n ℝ}
    (hM : PowerMPFamily N M) {a b : ℕ} (hab : a ≤ b) :
    rangeProj N M a * rangeProj N M b = rangeProj N M b := by
  have hpow : N ^ b = N ^ a * N ^ (b - a) := by
    rw [← pow_add, Nat.add_sub_of_le hab]
  unfold rangeProj
  calc
    (N ^ a * M a) * (N ^ b * M b) =
        (N ^ a * M a) * ((N ^ a * N ^ (b - a)) * M b) := by rw [hpow]
    _ = (N ^ a * M a * N ^ a) * (N ^ (b - a) * M b) := by
      simp only [mul_assoc]
    _ = N ^ a * (N ^ (b - a) * M b) := by rw [(hM a).aba_eq_a]
    _ = (N ^ a * N ^ (b - a)) * M b := by
      rw [mul_assoc]
    _ = N ^ b * M b := by rw [← hpow]

theorem rangeProj_mul_of_ge {N : Matrix n n ℝ} {M : ℕ → Matrix n n ℝ}
    (hM : PowerMPFamily N M) {a b : ℕ} (hab : a ≤ b) :
    rangeProj N M b * rangeProj N M a = rangeProj N M b := by
  calc
    rangeProj N M b * rangeProj N M a =
        (rangeProj N M b)ᵀ * (rangeProj N M a)ᵀ := by
          rw [rangeProj_symm hM b, rangeProj_symm hM a]
    _ = (rangeProj N M a * rangeProj N M b)ᵀ := by
      rw [Matrix.transpose_mul]
    _ = (rangeProj N M b)ᵀ := by rw [rangeProj_mul_of_le hM hab]
    _ = rangeProj N M b := rangeProj_symm hM b

theorem rangeProj_mul {N : Matrix n n ℝ} {M : ℕ → Matrix n n ℝ}
    (hM : PowerMPFamily N M) (a b : ℕ) :
    rangeProj N M a * rangeProj N M b = rangeProj N M (max a b) := by
  rcases le_total a b with hab | hba
  · rw [max_eq_right hab, rangeProj_mul_of_le hM hab]
  · rw [max_eq_left hba, rangeProj_mul_of_ge hM hba]

theorem shellProj_symm {N : Matrix n n ℝ} {M : ℕ → Matrix n n ℝ}
    (hM : PowerMPFamily N M) (m : ℕ) :
    (shellProj N M m)ᵀ = shellProj N M m := by
  unfold shellProj
  rw [Matrix.transpose_sub, rangeProj_symm hM m, rangeProj_symm hM (m + 1)]

theorem shellProj_idem {N : Matrix n n ℝ} {M : ℕ → Matrix n n ℝ}
    (hM : PowerMPFamily N M) (m : ℕ) :
    shellProj N M m * shellProj N M m = shellProj N M m := by
  unfold shellProj
  rw [sub_mul, mul_sub, mul_sub,
    rangeProj_mul_of_le hM (le_refl m),
    rangeProj_mul_of_le hM (Nat.le_succ m),
    rangeProj_mul_of_ge hM (Nat.le_succ m),
    rangeProj_mul_of_le hM (le_refl (m + 1))]
  abel

theorem shellProj_mul_of_lt {N : Matrix n n ℝ} {M : ℕ → Matrix n n ℝ}
    (hM : PowerMPFamily N M) {m r : ℕ} (hmr : m < r) :
    shellProj N M m * shellProj N M r = 0 := by
  unfold shellProj
  rw [sub_mul, mul_sub, mul_sub,
    rangeProj_mul_of_le hM (le_of_lt hmr),
    rangeProj_mul_of_le hM (le_of_lt (Nat.lt_succ_of_lt hmr)),
    rangeProj_mul_of_le hM (Nat.succ_le_of_lt hmr),
    rangeProj_mul_of_le hM (le_trans (Nat.succ_le_of_lt hmr) (Nat.le_succ r))]
  abel

theorem shellProj_orthogonal {N : Matrix n n ℝ} {M : ℕ → Matrix n n ℝ}
    (hM : PowerMPFamily N M) {m r : ℕ} (hne : m ≠ r) :
    shellProj N M m * shellProj N M r = 0 := by
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact shellProj_mul_of_lt hM hlt
  · calc
      shellProj N M m * shellProj N M r =
          (shellProj N M m)ᵀ * (shellProj N M r)ᵀ := by
            rw [shellProj_symm hM m, shellProj_symm hM r]
      _ = (shellProj N M r * shellProj N M m)ᵀ := by
        rw [Matrix.transpose_mul]
      _ = (0 : Matrix n n ℝ)ᵀ := by rw [shellProj_mul_of_lt hM hgt]
      _ = 0 := Matrix.transpose_zero

theorem rangeProj_zero {N : Matrix n n ℝ} {M : ℕ → Matrix n n ℝ}
    (hM : PowerMPFamily N M) : rangeProj N M 0 = 1 := by
  simpa [rangeProj, pow_zero] using (hM 0).aba_eq_a

lemma sum_range_sub_succ {G : Type*} [AddCommGroup G] (f : ℕ → G) :
    ∀ k : ℕ, (∑ m ∈ Finset.range k, (f m - f (m + 1))) = f 0 - f k
  | 0 => by simp
  | k + 1 => by
      rw [Finset.sum_range_succ, sum_range_sub_succ f k]
      abel

theorem shellProj_partition_of_unity {N : Matrix n n ℝ} {M : ℕ → Matrix n n ℝ}
    (hM : PowerMPFamily N M) {k : ℕ} (hNk : N ^ k = 0) :
    (∑ m ∈ Finset.range k, shellProj N M m) = 1 := by
  unfold shellProj
  rw [sum_range_sub_succ]
  rw [rangeProj_zero hM]
  have hk : rangeProj N M k = 0 := by
    unfold rangeProj
    rw [hNk, zero_mul]
  rw [hk, sub_zero]

theorem nilpotent_shell_projectors_orthogonal_partition
    {N : Matrix n n ℝ} {M : ℕ → Matrix n n ℝ}
    (hM : PowerMPFamily N M) {k : ℕ} (hNk : N ^ k = 0) :
    (∀ m, (shellProj N M m)ᵀ = shellProj N M m) ∧
    (∀ m, shellProj N M m * shellProj N M m = shellProj N M m) ∧
    (∀ m r, m ≠ r → shellProj N M m * shellProj N M r = 0) ∧
    ((∑ m ∈ Finset.range k, shellProj N M m) = 1) :=
  ⟨shellProj_symm hM, shellProj_idem hM,
    fun m r hne => shellProj_orthogonal hM hne,
    shellProj_partition_of_unity hM hNk⟩

end InfoGeometry.Singular.NilpotentShellFiltration
