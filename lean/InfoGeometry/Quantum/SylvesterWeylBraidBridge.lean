/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Weyl.WeylDisplacement
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic

/-!
# Single-Sheet Weyl Braid Relation for Sylvester Matrices
-/

namespace SylvesterWeylBraid

variable (n : ℕ) [NeZero n]
variable {R : Type*} [CommRing R]

def clockMatrix (ω : R) : Matrix (ZMod n) (ZMod n) R :=
  Matrix.of fun i j => if i = j then ω ^ i.val else 0

def shiftMatrix : Matrix (ZMod n) (ZMod n) R :=
  Matrix.of fun i j => if i = j + 1 then 1 else 0

lemma pow_eq_pow_mod (ω : R) (hn : ω ^ n = 1) (m : ℕ) :
    ω ^ m = ω ^ (m % n) := by
  have h : ω ^ m = ω ^ (n * (m / n) + m % n) := by rw [Nat.div_add_mod]
  rw [h, pow_add, pow_mul, hn, one_pow, one_mul]

lemma zmod_val_add_one (j : ZMod n) :
    (j + 1).val = (j.val + 1) % n := by
  have : (1 : ZMod n) = (1 : ℕ) := by simp
  rw [this, ZMod.val_add, ZMod.val_natCast]
  rw [Nat.add_mod, Nat.mod_mod, ←Nat.add_mod]

lemma pow_val_add_one (ω : R) (hn : ω ^ n = 1) (j : ZMod n) :
    ω ^ (j + 1).val = ω * ω ^ j.val := by
  rw [zmod_val_add_one n j]
  rw [← pow_eq_pow_mod n ω hn (j.val + 1)]
  rw [pow_succ, mul_comm]

theorem sylvester_weyl_braid_relation (ω : R) (hn : ω ^ n = 1) :
    clockMatrix n ω * shiftMatrix n = ω • (shiftMatrix n * clockMatrix n ω) := by
  ext i j
  rw [Matrix.mul_apply, Matrix.smul_apply, Matrix.mul_apply, smul_eq_mul]
  have hLHS : (∑ k : ZMod n, clockMatrix n ω i k * shiftMatrix n k j) =
      if i = j + 1 then ω ^ i.val else 0 := by
    have hsum : (∑ k : ZMod n, clockMatrix n ω i k * shiftMatrix n k j) =
        clockMatrix n ω i i * shiftMatrix n i j := by
      apply Finset.sum_eq_single i
      · intro k _ hk
        simp only [clockMatrix, Matrix.of_apply]
        have hne : ¬(i = k) := hk.symm
        rw [if_neg hne, zero_mul]
      · intro hi
        exact False.elim (hi (Finset.mem_univ i))
    have hval : clockMatrix n ω i i * shiftMatrix n i j =
        if i = j + 1 then ω ^ i.val else 0 := by
      simp only [clockMatrix, shiftMatrix, Matrix.of_apply, if_true]
      split_ifs with h
      · rw [mul_one]
      · rw [mul_zero]
    rw [hsum, hval]
  have hRHS : (∑ k : ZMod n, shiftMatrix n i k * clockMatrix n ω k j) =
      if i = j + 1 then ω ^ j.val else 0 := by
    have hsum : (∑ k : ZMod n, shiftMatrix n i k * clockMatrix n ω k j) =
        shiftMatrix n i j * clockMatrix n ω j j := by
      apply Finset.sum_eq_single j
      · intro k _ hk
        simp only [clockMatrix, Matrix.of_apply]
        rw [if_neg hk, mul_zero]
      · intro hj
        exact False.elim (hj (Finset.mem_univ j))
    have hval : shiftMatrix n i j * clockMatrix n ω j j =
        if i = j + 1 then ω ^ j.val else 0 := by
      simp only [clockMatrix, shiftMatrix, Matrix.of_apply, if_true]
      split_ifs with h
      · rw [one_mul]
      · rw [zero_mul]
    rw [hsum, hval]
  rw [hLHS, hRHS]
  split_ifs with h
  · rw [h]
    exact pow_val_add_one n ω hn j
  · rw [mul_zero]

end SylvesterWeylBraid
