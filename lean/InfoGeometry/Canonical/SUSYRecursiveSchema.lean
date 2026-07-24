import Mathlib
import InfoGeometry.Canonical.SuperAlgebraEquilibrium

/-!
# InfoGeometry.Canonical.SUSYRecursiveSchema

Recursive iterative schema specialized to the local SUSY seed
from `SuperAlgebraEquilibrium`.
-/

namespace InfoGeometry.Canonical.SUSYRecursiveSchema

open Matrix
open SuperAlgebraEquilibrium

abbrev M2R := Matrix (Fin 2) (Fin 2) ℝ

/-- Matrix commutator. -/
def comm (A X : M2R) : M2R := A * X - X * A

/-- Recursive iterated adjoint action `ad_A^n(X)`. -/
def adPow (A : M2R) : ℕ → M2R → M2R
  | 0, X => X
  | n + 1, X => comm A (adPow A n X)

@[simp] theorem adPow_zero (A X : M2R) :
    adPow A 0 X = X := rfl

@[simp] theorem adPow_succ (A : M2R) (n : ℕ) (X : M2R) :
    adPow A (n + 1) X = comm A (adPow A n X) := rfl

/-- First SUSY recursion step on `Q`: `ad_H(Q)=0`. -/
theorem adPow_H_Q_one :
    adPow H 1 Q = 0 := by
  simpa [adPow, comm] using super_even_odd_commute

/-- First SUSY recursion step on `Q_dag`: `ad_H(Q†)=0`. -/
theorem adPow_H_Qdag_one :
    adPow H 1 Q_dag = 0 := by
  unfold adPow comm H Q_dag
  -- `H = 1`, hence commutator with `H` vanishes.
  ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.mul_apply, Fin.sum_univ_two]

/-- Once zero is reached, all further recursive adjoint steps remain zero. -/
theorem adPow_zero_arg (A : M2R) :
    ∀ n : ℕ, adPow A n (0 : M2R) = 0 := by
  intro n
  induction n with
  | zero =>
      simp [adPow]
  | succ n ih =>
      simp [adPow, comm, ih]

/-- Recursive closure for `Q`: every positive-depth iterate vanishes. -/
theorem adPow_H_Q_succ_zero :
    ∀ n : ℕ, adPow H (n + 1) Q = 0 := by
  intro n
  induction n with
  | zero =>
      exact adPow_H_Q_one
  | succ n ih =>
      calc
        adPow H (Nat.succ (Nat.succ n)) Q
            = comm H (adPow H (Nat.succ n) Q) := by simp [adPow]
        _ = comm H 0 := by rw [ih]
        _ = 0 := by simp [comm]

/-- Recursive closure for `Q†`: every positive-depth iterate vanishes. -/
theorem adPow_H_Qdag_succ_zero :
    ∀ n : ℕ, adPow H (n + 1) Q_dag = 0 := by
  intro n
  induction n with
  | zero =>
      exact adPow_H_Qdag_one
  | succ n ih =>
      calc
        adPow H (Nat.succ (Nat.succ n)) Q_dag
            = comm H (adPow H (Nat.succ n) Q_dag) := by simp [adPow]
        _ = comm H 0 := by rw [ih]
        _ = 0 := by simp [comm]

/-- Full iterative closure: for all positive depths, `ad_H^n(Q)=0`. -/
theorem adPow_H_Q_of_pos :
    ∀ n : ℕ, 0 < n → adPow H n Q = 0 := by
  intro n hn
  rcases Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn) with ⟨k, rfl⟩
  simpa using adPow_H_Q_succ_zero k

/-- Full iterative closure: for all positive depths, `ad_H^n(Q†)=0`. -/
theorem adPow_H_Qdag_of_pos :
    ∀ n : ℕ, 0 < n → adPow H n Q_dag = 0 := by
  intro n hn
  rcases Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn) with ⟨k, rfl⟩
  simpa using adPow_H_Qdag_succ_zero k

end InfoGeometry.Canonical.SUSYRecursiveSchema
