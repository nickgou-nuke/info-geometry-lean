/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Ring

/-!
# The `(3,1;1,3)` recurrence and its Hadamard coordinates

The recursively constructed pair starts at `(1,0)`. Its sum and difference
are exactly `4^k` and `2^k`. The difference is first expressed without truncated
natural subtraction, as `M_k = S_k + 2^k`.

This is a finite-iteration and integer-matrix result. Identifying these numbers
with dimensions or cardinalities of a Clifford tensor basis requires a separate
basis construction and counting theorem.
-/

namespace InfoGeometry.Algebra.HadamardRecurrence

/-- The natural-number orbit of the recurrence. -/
def counts : ℕ → ℕ × ℕ :=
  Nat.rec (motive := fun _ => ℕ × ℕ) (1, 0)
    (fun _ p => (3 * p.1 + p.2, p.1 + 3 * p.2))

@[simp] theorem counts_zero : counts 0 = (1, 0) := rfl

@[simp] theorem counts_succ (k : ℕ) :
    counts (k + 1) =
      (3 * (counts k).1 + (counts k).2, (counts k).1 + 3 * (counts k).2) := rfl

/-- The symmetric Hadamard coordinate grows by four at each step. -/
theorem sum_eq_four_pow (k : ℕ) : (counts k).1 + (counts k).2 = 4 ^ k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change (3 * (counts k).1 + (counts k).2) +
      ((counts k).1 + 3 * (counts k).2) = 4 ^ (k + 1)
    calc
      _ = ((counts k).1 + (counts k).2) * 4 := by ring
      _ = 4 ^ (k + 1) := by rw [ih, pow_succ]

/-- The antisymmetric Hadamard coordinate grows by two at each step. -/
theorem fst_eq_snd_add_two_pow (k : ℕ) :
    (counts k).1 = (counts k).2 + 2 ^ k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change 3 * (counts k).1 + (counts k).2 =
      ((counts k).1 + 3 * (counts k).2) + 2 ^ (k + 1)
    rw [ih, pow_succ]
    ring

theorem difference_eq_two_pow (k : ℕ) :
    (counts k).1 - (counts k).2 = 2 ^ k := by
  rw [fst_eq_snd_add_two_pow]
  exact Nat.add_sub_cancel_left _ _

/-- No division or parity side condition is needed for the doubled closed forms. -/
theorem twice_fst (k : ℕ) : 2 * (counts k).1 = 4 ^ k + 2 ^ k := by
  calc
    2 * (counts k).1 = (counts k).1 + (counts k).1 := by omega
    _ = (counts k).1 + ((counts k).2 + 2 ^ k) := by
      rw [← fst_eq_snd_add_two_pow]
    _ = 4 ^ k + 2 ^ k := by rw [← add_assoc, sum_eq_four_pow]

theorem twice_snd (k : ℕ) : 2 * (counts k).2 + 2 ^ k = 4 ^ k := by
  have hs := sum_eq_four_pow k
  have hd := fst_eq_snd_add_two_pow k
  omega

theorem snd_le_fst (k : ℕ) : (counts k).2 ≤ (counts k).1 := by
  rw [fst_eq_snd_add_two_pow]
  exact Nat.le_add_right _ _

theorem fst_le_four_pow (k : ℕ) : (counts k).1 ≤ 4 ^ k := by
  have h := sum_eq_four_pow k
  omega

theorem two_pow_le_four_pow (k : ℕ) : (2 : ℕ) ^ k ≤ 4 ^ k := by
  have hs := sum_eq_four_pow k
  have hd := fst_eq_snd_add_two_pow k
  omega

/-- The integer recurrence matrix. -/
def transition : Matrix (Fin 2) (Fin 2) ℤ := !![3, 1; 1, 3]

/-- Unnormalized Hadamard change of coordinates, valid integrally. -/
def hadamard : Matrix (Fin 2) (Fin 2) ℤ := !![1, 1; 1, -1]

/-- The diagonal spectral action on sum and difference. -/
def spectral : Matrix (Fin 2) (Fin 2) ℤ := !![4, 0; 0, 2]

/-- An exact matrix intertwining, without adjoining a square root of two. -/
theorem hadamard_transition : hadamard * transition = spectral * hadamard := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [hadamard, transition, spectral, Matrix.mul_apply, Fin.sum_univ_two]

/-- The unnormalized Hadamard matrix is a similitude of factor two. -/
theorem hadamard_square : hadamard * hadamard = (2 : ℤ) • (1 : Matrix (Fin 2) (Fin 2) ℤ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [hadamard, Matrix.mul_apply, Fin.sum_univ_two]

/-- The two genuine operators do not commute; the spectral intertwining is ordered. -/
theorem transition_hadamard_noncommuting :
    transition * hadamard ≠ hadamard * transition := by
  intro h
  have h01 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℤ => M 0 1) h
  norm_num [transition, hadamard, Matrix.mul_apply, Fin.sum_univ_two] at h01

end InfoGeometry.Algebra.HadamardRecurrence
